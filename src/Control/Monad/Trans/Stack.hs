{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{- |
Module: Control.Monad.Trans.Stack
Description: Reified monad transformer stacks
Copyright: (c) Samuel Schlesinger 2020
License: MIT
Maintainer: sgschlesinger@gmail.com
Stability: experimental
Portability: POSIX, Windows
-}
module Control.Monad.Trans.Stack where

import GHC.TypeLits (Nat, type (+), type (-), ErrorMessage(..), TypeError)
import Data.Coerce (coerce)
import Control.Monad.Trans (MonadTrans(lift))
import Control.Monad.Reader(ReaderT(..))

{- |
A computation consisting of a stack of monad transformers and a base monad.
-}
newtype Stack (ts :: [(* -> *) -> * -> *]) (m :: * -> *) a = Stack { runStack :: Stack' ts m a }

{- |
The type family which we interleave with 'Stack' for its implementation.
-}
type family Stack' (ts :: [(* -> *) -> * -> *]) (m :: * -> *) :: * -> * where
  Stack' (t ': ts) m = t (Stack ts m)
  Stack'    '[]    m = m

instance Functor f => Functor (Stack '[] f) where
  fmap phi (Stack fa) = Stack (fmap phi fa)

instance
  ( forall f'. Monad f' => Monad (t f')
  , Monad f
  , Monad (Stack ts f)
  ) => Functor (Stack (t ': ts) f) where
  fmap phi (Stack fa) = Stack (fmap phi fa)

instance Applicative f => Applicative (Stack '[] f) where
  Stack ff <*> Stack fx = Stack (ff <*> fx)
  pure = Stack . pure

instance
  ( forall f'. Monad f' => Monad (t f')
  , Monad f
  , Monad (Stack ts f)
  ) => Applicative (Stack (t ': ts) f)
  where
  Stack ff <*> Stack fx = Stack (ff <*> fx)
  pure = Stack . pure

instance
  ( Monad f
  ) => Monad (Stack '[] f)
  where
  Stack x >>= f = Stack (x >>= runStack . f) 
instance
  ( forall f'. Monad f' => Monad (t f')
  , MonadTrans t
  , Monad f
  , Monad (Stack ts f)
  ) => Monad (Stack (t ': ts) f)
  where
  Stack x >>= f = Stack (x >>= runStack . f) 

instance MonadTrans (Stack '[])
  where
  lift = Stack

instance
  ( forall f'. Monad f' => Monad (t f')
  , MonadTrans t
  , forall f'. Monad f' => Monad (Stack ts f')
  , MonadTrans (Stack ts)
  ) => MonadTrans (Stack (t ': ts))
  where
  lift = Stack . lift . lift

-- | Computes a substack, or a suffix, of the given stack of monad
-- transformers.
type family Substack n ts f where
  Substack  'Z     (t ': ts) f = t (Stack ts f)
  Substack  ('S n) (t ': ts) f = Substack n ts f

-- | Type level natural numbers.
data N = S N | Z

-- | Greater than constraint.
class (n :: N) > (m :: N)

instance 'S n > 'Z

instance n > m => 'S n > m

-- | A type family used to lift substacks up into the full 'Stack'
-- computation.
class Uplift n ts f where
  liftSubstack :: Substack n ts f a -> Stack ts f a

instance Uplift 'Z (t ': ts) f where
  liftSubstack fa = Stack fa

instance
  ( MonadTrans t
  , MonadTrans (Stack (t ': ts))
  , Monad (Stack ts f)
  , Uplift n ts f
  ) => Uplift ('S n) (t ': ts) f where
  liftSubstack fa = Stack $ lift (liftSubstack @n fa)

-- | Computes the index of an item in a type level list.
type family IndexIn t ts where
  IndexIn t (t ': ts)  = 'Z
  IndexIn t (t' ': ts) = 'S (IndexIn t ts)
  IndexIn t ts = TypeError ('Text "Could not find " ':<>: 'ShowType t ':<>: 'Text " in list " ':<>: 'ShowType ts)

{- |
Lifts a substack, or a suffix, of the 'Stack' all the way up into the 'Stack' computation.
Expected to be used with TypeApplications.
-}
uplift :: forall t ts f a. Uplift (IndexIn t ts) ts f => Substack (IndexIn t ts) ts f a -> Stack ts f a
uplift = liftSubstack @(IndexIn t ts) @ts @f @a

-- | A 'Runner' for a stack of transformers in an arbitrary monad.
newtype Runner ts = Runner (forall f a. Monad f => Stack ts f a -> f a)

-- | Laws:
-- (runner >>= \phi -> run phi (x >>= f)) == (runner >>= \phi -> run phi x >>= run phi f)
class WithRunner ts where
  runner :: (Monad f, Monad (Stack ts f)) => Stack ts f (Runner ts)
  runner = withRunner pure
  withRunner :: (Monad f, Monad (Stack ts f)) => (Runner ts -> Stack ts f a) -> Stack ts f a
  withRunner = (runner >>=)

-- | The class of 'Representable' transformers. Basically, these can be
-- constant size containers or functions, or arbitrary combination of the two.
class Representable t where
  type Rep t
  tabulate :: (Rep t -> f a) -> t f a
  index :: t f a -> Rep t -> f a

instance Representable (ReaderT r) where
  type Rep (ReaderT r) = r
  tabulate = ReaderT 
  index = runReaderT

instance WithRunner '[] where
  runner = pure $ Runner runStack

instance (Representable t, WithRunner ts, forall f. Monad f => Monad (t f), forall f. Monad f => Monad (Stack ts f), MonadTrans t) => WithRunner (t ': ts) where
  runner = do
    phi <- Stack (lift runner)
    Stack do
      rep <- tabulate pure
      pure (Runner $ \action -> phi `run` index (runStack action) rep)

-- | Run a stack with a 'Runner'
run :: Monad f => Runner ts -> Stack ts f a -> f a
run (Runner phi) stack = phi stack
