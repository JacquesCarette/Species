{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module FinIsos ( finSum, finSumInv, finPair, finPairInv ) where

import Control.Arrow ((+++), (***))

import Equality
import Nat

import Unsafe.Coerce

------------------------------------------------------------
-- Preliminaries
------------------------------------------------------------

--------------------------------------------------
-- Properties of addition and multiplication

plusZeroR :: SNat n -> Plus n Z == n
plusZeroR SZ     = Refl
plusZeroR (SS n) = case plusZeroR n of Refl -> Refl

plusSuccR :: SNat m -> SNat n -> Plus m (S n) == S (Plus m n)
plusSuccR SZ _     = Refl
plusSuccR (SS m) n = case plusSuccR m n of Refl -> Refl

plusAssoc :: SNat a -> SNat b -> SNat c -> (Plus (Plus a b) c) == Plus a (Plus b c)
plusAssoc SZ _ _ = Refl
plusAssoc (SS a) b c = case plusAssoc a b c of Refl -> Refl

plusComm :: SNat a -> SNat b -> Plus a b == Plus b a
plusComm SZ b = case plusZeroR b of Refl -> Refl
plusComm (SS a) b = case (plusSuccR b a, plusComm a b) of (Refl, Refl) -> Refl

mulZeroR :: SNat x -> Times x Z == Z
mulZeroR SZ = Refl
mulZeroR (SS x) = mulZeroR x

--------------------------------------------------
-- Less-than-or-equal, less-than, and properties thereof

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

lteTrans :: x <= y -> y <= z -> x <= z
lteTrans LTEZ _ = LTEZ
lteTrans (LTES xLTy) (LTES yLTz) = LTES (lteTrans xLTy yLTz)

lte_ltTrans :: x <= y -> y < z -> x < z
lte_ltTrans xLTy yLTz = lteTrans (LTES xLTy) yLTz

lt__lte :: SNat x -> SNat y -> x < y -> x <= y
lt__lte SZ _ _ = LTEZ
lt__lte (SS x) SZ lt = absurdLT lt
lt__lte (SS x) (SS y) (LTES lt) = LTES (lt__lte x y lt)

lteDecomp :: SNat x -> SNat y -> x <= y -> Either (x == y) (x < y)
lteDecomp SZ SZ _ = Left Refl
lteDecomp SZ (SS y) _ = Right (LTES LTEZ)
lteDecomp (SS x) SZ lt = absurdLT lt
lteDecomp (SS x) (SS y) (LTES lte) =
  case lteDecomp x y lte of
    Left Refl -> Left Refl
    Right lt -> Right (LTES lt)

lteSuccContra :: SNat x -> S x <= x -> a
lteSuccContra SZ le = absurdLT le
lteSuccContra (SS x) (LTES p) = lteSuccContra x p

plusMono :: SNat n -> m <= n -> x <= y -> (Plus m x) <= (Plus n y)
plusMono _ LTEZ LTEZ               = LTEZ
plusMono n LTEZ (LTES xLTy)        = ltePlus n (LTES xLTy)
plusMono (SS n) (LTES mLTn) (xLTy) = LTES (plusMono n mLTn xLTy)

timesMono :: SNat y -> m <= n -> x <= y -> (Times m x) <= (Times n y)
timesMono _ LTEZ _ = LTEZ
timesMono y (LTES mLTn) xLTy = plusMono y xLTy (timesMono y mLTn xLTy)

lteCancelPlusR :: SNat m -> SNat n -> SNat x -> (Plus m x <= Plus n x) -> (m <= n)
lteCancelPlusR m n SZ lte = case (plusZeroR m, plusZeroR n) of (Refl, Refl) -> lte
lteCancelPlusR m n (SS x) lte =
  case (plusSuccR m x, plusSuccR n x) of
    (Refl, Refl) -> lteInj (lteCancelPlusR (SS m) (SS n) x lte)

lteCancelPlusL :: SNat i -> Plus i j <= Plus i k -> j <= k
lteCancelPlusL SZ le = le
lteCancelPlusL (SS i) (LTES le) = lteCancelPlusL i le

lteCancelMulR :: SNat i -> SNat j -> SNat k -> Times i (S k) <= Times j (S k) -> i <= j
lteCancelMulR SZ _ _ _ = LTEZ
lteCancelMulR (SS i) SZ _ le = absurdLT le
lteCancelMulR (SS i) (SS j) k le = LTES (lteCancelMulR i j k (lteCancelPlusL (SS k) le))

ltCancelMulR :: SNat i -> SNat m -> SNat n -> Times i n < Times m n -> i < m
ltCancelMulR i m SZ le = case (mulZeroR m, mulZeroR i) of (Refl, Refl) -> absurdLT le
ltCancelMulR i m (SS n) le =
  case lteDecomp i m (lteCancelMulR i m n (lt__lte (times i (SS n)) (times m (SS n)) le)) of
    Left Refl -> lteSuccContra (times m (SS n)) le
    Right lt  -> lt

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
-- Division algorithm

data Div x n where
  Div :: SNat i -> SNat j -> (j < n) -> (x == Plus j (Times i n)) -> Div x n

divisionAlg :: SNat x -> SNat n -> Div x n
divisionAlg x n = case decLT n x of
  Left lt -> case plusZeroR x of Refl -> Div SZ x lt Refl
  Right (Minus x' Refl) ->
    case divisionAlg x' n of
      Div i' j lt Refl ->
        case (plusAssoc j (times i' n) n, plusComm (times i' n) n) of
          (Refl, Refl) ->
            Div (SS i') j lt Refl

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
    Right (Minus j Refl) -> Left (FinN j (lteCancelPlusR (SS j) m n xLTmn))

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

finNProdInv :: SNat m -> SNat n -> FinN (Times m n) -> (FinN m, FinN n)
finNProdInv m n (FinN x xlt) = case divisionAlg x n of
  Div i j jlt Refl ->
    ( FinN i (ltCancelMulR i m n
               (lte_ltTrans
                 (ltePlus j (lteRefl (times i n)))
                 xlt
               )
             )
    , FinN j jlt
    )

finPairInv :: SNat m -> SNat n -> Fin (Times m n) -> (Fin m, Fin n)
finPairInv m n = (finNToFin *** finNToFin) . finNProdInv m n . finToFinN
