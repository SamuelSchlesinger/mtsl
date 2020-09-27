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
import Control.Monad.Writer (WriterT, tell)
import Control.Monad.State (StateT, get)

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

-- | A type family used to lift substacks up into the full 'Stack'
-- computation.
class Uplift n ts f where
  uplift :: Substack n ts f a -> Stack ts f a

instance Uplift 'Z (t ': ts) f where
  uplift fa = Stack fa

instance
  ( MonadTrans t
  , MonadTrans (Stack (t ': ts))
  , Monad (Stack ts f)
  , Uplift n ts f
  ) => Uplift ('S n) (t ': ts) f where
  uplift fa = Stack $ lift (uplift @n fa)

-- | Computes the index of an item in a type level list.
type family IndexIn t ts where
  IndexIn t (t ': ts)  = 'Z
  IndexIn t (t' ': ts) = 'S (IndexIn t ts)
  IndexIn t ts = TypeError ('Text "Could not find " ':<>: 'ShowType t ':<>: 'Text " in list " ':<>: 'ShowType ts)

{- |
Lifts a substack, or a suffix, of the 'Stack' all the way up into the 'Stack' computation.
Expected to be used with TypeApplications.
-}
substack :: forall t ts f a. Uplift (IndexIn t ts) ts f => Substack (IndexIn t ts) ts f a -> Stack ts f a
substack = uplift @(IndexIn t ts) @ts @f @a
