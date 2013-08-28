{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators  #-}

module Data.Type.Nat.Inequality where

import Data.Type.Equality
import Data.Type.Nat

import Unsafe.Coerce

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
lt__lte (SS _) SZ lt = absurdLT lt
lt__lte (SS x) (SS y) (LTES lt) = LTES (lt__lte x y lt)

lteDecomp :: SNat x -> SNat y -> x <= y -> Either (x :=: y) (x < y)
lteDecomp SZ SZ _ = Left Refl
lteDecomp SZ (SS _) _ = Right (LTES LTEZ)
lteDecomp (SS _) SZ lt = absurdLT lt
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
lteCancelMulR (SS _) SZ _ le = absurdLT le
lteCancelMulR (SS i) (SS j) k le = LTES (lteCancelMulR i j k (lteCancelPlusL (SS k) le))

ltCancelMulR :: SNat i -> SNat m -> SNat n -> Times i n < Times m n -> i < m
ltCancelMulR i m SZ le = case (mulZeroR m, mulZeroR i) of (Refl, Refl) -> absurdLT le
ltCancelMulR i m (SS n) le =
  case lteDecomp i m (lteCancelMulR i m n (lt__lte (times i (SS n)) (times m (SS n)) le)) of
    Left Refl -> lteSuccContra (times m (SS n)) le
    Right lt  -> lt

