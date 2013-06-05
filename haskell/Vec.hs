{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds      #-}

module Vec where

import Prelude hiding (concat, unzip)

import Control.Lens
import Finite
import Nat (Nat(..), Fin(..), SNat(..), Plus, Times)
import Proxy
import Util

data Vec :: Nat -> * -> * where
  VNil :: Vec Z a
  VCons :: a -> Vec n a -> Vec (S n) a

instance Functor (Vec n) where
  fmap _ VNil = VNil
  fmap f (VCons a v) = VCons (f a) (fmap f v)

data Vec' :: * -> * where
  SomeVec :: Vec n a -> Vec' a

vnil' :: Vec' a
vnil' = SomeVec VNil

vcons' :: a -> Vec' a -> Vec' a
vcons' a (SomeVec v) = SomeVec (VCons a v)

fromList :: [a] -> Vec' a
fromList []     = vnil'
fromList (a:as) = vcons' a (fromList as)

singleton :: a -> Vec (S Z) a
singleton a = VCons a VNil

tail :: Vec (S n) a -> Vec n a
tail (VCons _ v) = v

vIndex :: Vec n a -> Fin n -> a
vIndex (VCons a _) FZ     = a
vIndex (VCons _ v) (FS f) = vIndex v f

unzip :: Vec n (a,b) -> (Vec n a, Vec n b)
unzip VNil = (VNil, VNil)
unzip (VCons (a,b) v) = (VCons a va, VCons b vb)
  where (va,vb) = unzip v

fins :: SNat n -> Vec n (Fin n)
fins SZ     = VNil
fins (SS n) = VCons FZ (fmap FS (fins n))

enumerate :: forall l. Finite l => Vec (Size l) l
enumerate = fmap (view finite) (fins (size (Proxy :: Proxy l)))

append :: Vec k l -> Vec k' l -> Vec (Plus k k') l
append VNil v = v
append (VCons a v) v' = VCons a (append v v')

append' :: Vec' l -> Vec' l -> Vec' l
append' (SomeVec VNil) v         = v
append' (SomeVec (VCons a v)) v' = vcons' a (append' (SomeVec v) v')

concat :: Vec i (Vec j a) -> Vec (Times i j) a
concat VNil = VNil
concat (VCons v vs) = append v (concat vs)

concat' :: Vec k (Vec' a) -> Vec' a
concat' VNil = SomeVec VNil
concat' (VCons v vs) = append' v (concat' vs)

------------------------------------------------------------
-- HVec: Length-indexed, type-indexed heterogeneous vectors
------------------------------------------------------------

data HVec :: Nat -> [*] -> * where
  HNil   :: HVec Z '[]
  HCons  :: l -> HVec n ls -> HVec (S n) (l ': ls)

toHVec :: Vec n a -> HVec n (Replicate n a)
toHVec VNil        = HNil
toHVec (VCons a v) = HCons a (toHVec v)

hProxy :: HVec n ls -> LProxy n ls
hProxy HNil               = LNil
hProxy (HCons (_ :: l) h) = LCons (Proxy :: Proxy l) (hProxy h)

-- Given a heterogeneous vector of vectors with sizes (n1, n2, ...),
-- concatenate them to give a single vector of size (n1 + n2 + ...).
hconcat :: Proxy g -> LProxy n l2s -> HVec n (VecsOfSize l2s a) -> Vec (Size (Sum l2s)) a
hconcat _ LNil HNil                 = VNil
hconcat p (LCons _ ls) (HCons v vs) = append v (hconcat p ls vs)

-- Essentially, VecsOfSize ls a = Map ((\n -> Vec n a) . Size) ls, but
-- we can't write that explicitly, because (1) no type-level lambdas
-- and (2) Size has to be fully applied.
type family VecsOfSize (ls :: [*]) (a :: *) :: [*]
type instance VecsOfSize '[] a         = '[]
type instance VecsOfSize (l ': ls) a = (Vec (Size l) a ': VecsOfSize ls a)
