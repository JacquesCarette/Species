{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeOperators        #-}


module Nat where

import Control.Lens

import Unsafe.Coerce  -- for eliminating Fin Z

------------------------------------------------------------
-- Natural numbers

data Nat = Z | S Nat
  deriving (Eq, Ord, Show)

nat :: r -> (r -> r) -> Nat -> r
nat z s Z     = z
nat z s (S n) = s (nat z s n)

natToInt :: Nat -> Int
natToInt = nat 0 succ

intToNat :: Int -> Nat
intToNat 0 = Z
intToNat n = S (intToNat (n-1))

------------------------------------------------------------
-- Singleton Nats

data SNat :: Nat -> * where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

deriving instance Show (SNat n)

snat :: r -> (r -> r) -> SNat n -> r
snat z s SZ     = z
snat z s (SS n) = s (snat z s n)

snatToInt :: SNat n -> Int
snatToInt = snat 0 succ

snatEq :: SNat m -> SNat n -> Bool
snatEq SZ SZ         = True
snatEq (SS m) (SS n) = snatEq m n
snatEq _ _           = False

class Natural (n :: Nat) where
  toSNat :: SNat n

instance Natural Z where
  toSNat = SZ

instance Natural n => Natural (S n) where
  toSNat = SS toSNat

type family Plus (m :: Nat) (n :: Nat) :: Nat
type instance Plus Z n     = n
type instance Plus (S m) n = S (Plus m n)

plus :: SNat m -> SNat n -> SNat (Plus m n)
plus SZ n     = n
plus (SS m) n = SS (plus m n)

type family Times (m :: Nat) (n :: Nat) :: Nat
type instance Times Z n     = Z
type instance Times (S m) n = Plus n (Times m n)

times :: SNat m -> SNat n -> SNat (Times m n)
times SZ _     = SZ
times (SS m) n = plus n (times m n)

------------------------------------------------------------
-- Finite types

data Fin :: Nat -> * where
  FZ :: Fin (S n)
  FS :: Fin n -> Fin (S n)

deriving instance Show (Fin n)
deriving instance Eq (Fin n)

fin :: r -> (r -> r) -> Fin n -> r
fin z s FZ     = z
fin z s (FS n) = s (fin z s n)

finToInt :: Fin n -> Int
finToInt = fin 0 succ

absurd :: Fin Z -> a
absurd = unsafeCoerce

data (<=) :: Nat -> Nat -> * where
  LTEZ :: Z <= n
  LTES :: m <= n -> S m <= S n

lteRefl :: SNat n -> n <= n
lteRefl SZ     = LTEZ
lteRefl (SS n) = LTES (lteRefl n)

lteInj :: S m <= S n -> m <= n
lteInj (LTES pf) = pf

lteS :: m <= n -> m <= S n
lteS LTEZ      = LTEZ
lteS (LTES pf) = LTES (lteS pf)

ltePlus :: SNat x -> m <= n -> m <= (Plus x n)
ltePlus SZ pf     = pf
ltePlus (SS x) pf = lteS (ltePlus x pf)

plusMono :: SNat n -> m <= n -> x <= y -> (Plus m x) <= (Plus n y)
plusMono _ LTEZ LTEZ               = LTEZ
plusMono n LTEZ (LTES xLTy)        = ltePlus n (LTES xLTy)
plusMono (SS n) (LTES mLTn) (xLTy) = LTES (plusMono n mLTn xLTy)

timesMono :: SNat y -> m <= n -> x <= y -> (Times m x) <= (Times n y)
timesMono _ LTEZ _ = LTEZ
timesMono y (LTES mLTn) xLTy = plusMono y xLTy (timesMono y mLTn xLTy)

type m < n = S m <= n

absurdLT :: (i < Z) -> a
absurdLT = unsafeCoerce

data FinN :: Nat -> * where
  FinN :: SNat i -> (i < n) -> FinN n

finToFinN :: Fin n -> FinN n
finToFinN FZ     = FinN SZ (LTES LTEZ)
finToFinN (FS i) =
  case finToFinN i of
    (FinN j jLTn) -> FinN (SS j) (LTES jLTn)

finNToFin :: FinN n -> Fin n
finNToFin (FinN SZ (LTES _))        = FZ
finNToFin (FinN (SS i) (LTES iLTn)) = FS (finNToFin (FinN i iLTn))

finNProd :: SNat m -> SNat n -> FinN m -> FinN n -> FinN (Times m n)
finNProd SZ     _ (FinN _ iLTZ) _             = absurdLT iLTZ
finNProd (SS m) n (FinN i iLTm) (FinN j jLTn)
    = FinN (j `plus` (i `times` n)) finNProdPf
  where
    finNProdPf = plusMono n jLTn (timesMono n (lteInj iLTm) (lteRefl n))

finPair :: SNat m -> SNat n -> Fin m -> Fin n -> Fin (Times m n)
finPair m n i j = finNToFin (finNProd m n (finToFinN i) (finToFinN j))

--------------------------------------------------
-- Enumerating all the elements of Fin n

fins :: SNat n -> [Fin n]
fins SZ     = []
fins (SS n) = FZ : map FS (fins n)
