{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds      #-}

module Vec where

import Control.Lens
import Finite
import Nat (Nat(..), Fin(..), SNat(..), Plus)
import Proxy

data Vec :: Nat -> * -> * where
  VNil :: Vec Z a
  VCons :: a -> Vec n a -> Vec (S n) a

instance Functor (Vec n) where
  fmap _ VNil = VNil
  fmap f (VCons a v) = VCons (f a) (fmap f v)

singleton :: a -> Vec (S Z) a
singleton a = VCons a VNil

tail :: Vec (S n) a -> Vec n a
tail (VCons _ v) = v

vIndex :: Vec n a -> Fin n -> a
vIndex (VCons a _) FZ     = a
vIndex (VCons _ v) (FS f) = vIndex v f

fins :: SNat n -> Vec n (Fin n)
fins SZ     = VNil
fins (SS n) = VCons FZ (fmap FS (fins n))

enumerate :: forall l. Finite l => Vec (Size l) l
enumerate = fmap (view finite) (fins (size (Proxy :: Proxy l)))

concat :: Vec k l -> Vec k' l -> Vec (Plus k k') l
concat VNil v = v
concat (VCons a v) v' = VCons a (Vec.concat v v')

data Vec' :: * -> * where
  SomeVec :: Vec n a -> Vec' a

fromList :: [a] -> Vec' a
fromList [] = SomeVec VNil
fromList (a:as) =
  case fromList as of
    SomeVec v -> SomeVec (VCons a v)
