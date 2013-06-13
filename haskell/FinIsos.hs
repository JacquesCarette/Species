{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
module FinIsos where

import Control.Arrow ((+++), (***))

import Equality
import Nat

import Unsafe.Coerce

------------------------------------------------------------
-- Preliminaries
------------------------------------------------------------

--------------------------------------------------
-- Less-than-or-equal and properties thereof

data (<=) :: Nat -> Nat -> * where
  LTEZ :: Z <= n
  LTES :: m <= n -> S m <= S n

type m < n = S m <= n

absurdLT :: (i < Z) -> a
absurdLT = unsafeCoerce

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

--------------------------------------------------
-- Properties of addition and multiplication

plusZeroR :: SNat n -> Plus n Z == n
plusZeroR SZ     = Refl
plusZeroR (SS n) = case plusZeroR n of Refl -> Refl

plusSuccR :: SNat m -> SNat n -> Plus m (S n) == S (Plus m n)
plusSuccR SZ _     = Refl
plusSuccR (SS m) n = case plusSuccR m n of Refl -> Refl

plusCancelR :: SNat m -> SNat n -> SNat x -> (Plus m x <= Plus n x) -> (m <= n)
plusCancelR m n SZ lte = case (plusZeroR m, plusZeroR n) of (Refl, Refl) -> lte
plusCancelR m n (SS x) lte =
  case (plusSuccR m x, plusSuccR n x) of
    (Refl, Refl) -> lteInj (plusCancelR (SS m) (SS n) x lte)

--------------------------------------------------
-- Type-level subtraction and decidable ordering

data Minus x n where
  Minus :: SNat j -> (x == Plus j n) -> Minus x n

decLT :: SNat n -> SNat x -> Either (x < n) (x `Minus` n)
decLT SZ x = case plusZeroR x of Refl -> Right (Minus x Refl)
decLT (SS n) SZ = Left (LTES LTEZ)
decLT (SS n) (SS x) = case decLT n x of
  Left xLTn            -> Left (LTES xLTn)
  Right (Minus j Refl) -> case plusSuccR j n of Refl -> Right (Minus j Refl)

--------------------------------------------------
-- FinN

-- FinN n is isomorphic to Fin n, but much easier to work with
-- directly, since it lets us do arithmetic and construct the
-- necessary proofs separately.

data FinN :: Nat -> * where
  FinN :: SNat i -> (i < n) -> FinN n

-- Conversion functions witnessing the isomorphism.

finToFinN :: Fin n -> FinN n
finToFinN FZ     = FinN SZ (LTES LTEZ)
finToFinN (FS i) =
  case finToFinN i of
    (FinN j jLTn) -> FinN (SS j) (LTES jLTn)

finNToFin :: FinN n -> Fin n
finNToFin (FinN SZ (LTES _))        = FZ
finNToFin (FinN (SS i) (LTES iLTn)) = FS (finNToFin (FinN i iLTn))

--------------------------------------------------
-- Sum of Fins: Either (Fin m) (Fin n) <-> Fin (m + n)

-- forward direction

finNSum :: SNat m -> SNat n -> Either (FinN m) (FinN n) -> FinN (Plus m n)
finNSum m n (Left (FinN i iLTm))  = FinN (plus i n) (plusMono m iLTm (lteRefl n))
finNSum m n (Right (FinN j jLTn)) = FinN j (ltePlus m jLTn)

finSum :: SNat m -> SNat n -> Either (Fin m) (Fin n) -> Fin (Plus m n)
finSum m n = finNToFin . finNSum m n . (finToFinN +++ finToFinN)

-- backward direction

finNSumInv :: SNat m -> SNat n -> FinN (Plus m n) -> Either (FinN m) (FinN n)
finNSumInv m n (FinN x xLTmn) =
  case decLT n x of
    Left xLTn -> Right (FinN x xLTn)
    Right (Minus j Refl) -> Left (FinN j (plusCancelR (SS j) m n xLTmn))

finSumInv :: SNat m -> SNat n -> Fin (Plus m n) -> Either (Fin m) (Fin n)
finSumInv m n = (finNToFin +++ finNToFin) . finNSumInv m n . finToFinN

--------------------------------------------------
-- Product of Fins: Fin (m * n) <-> (Fin m, Fin n)

-- forward direction

finNProd :: SNat m -> SNat n -> (FinN m, FinN n) -> FinN (Times m n)
finNProd SZ     _ (FinN _ iLTZ, _)             = absurdLT iLTZ
finNProd (SS m) n (FinN i iLTm, FinN j jLTn)
    = FinN (j `plus` (i `times` n)) finNProdPf
  where
    finNProdPf = plusMono n jLTn (timesMono n (lteInj iLTm) (lteRefl n))

finPair :: SNat m -> SNat n -> (Fin m, Fin n) -> Fin (Times m n)
finPair m n = finNToFin . finNProd m n . (finToFinN *** finToFinN)
