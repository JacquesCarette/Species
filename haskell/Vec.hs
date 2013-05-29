{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds      #-}

module Vec where

import Nat

data Vec :: Nat -> * -> * where
  VNil :: Vec Z a
  VCons :: a -> Vec n a -> Vec (S n) a

instance Functor (Vec n) where
  fmap _ VNil = VNil
  fmap f (VCons a v) = VCons (f a) (fmap f v)

singleton :: a -> Vec (S Z) a
singleton a = VCons a VNil

