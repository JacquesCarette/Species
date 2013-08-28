{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators  #-}

module Data.Fin.Isos where

import           Control.Arrow            ((***), (+++))

import           Data.Fin
import           Data.Type.Equality
import           Data.Type.Nat
import           Data.Type.Nat.Div
import           Data.Type.Nat.Inequality
import           Data.Type.Nat.Minus

--------------------------------------------------
-- Sum of Fins: Either (Fin m) (Fin n) <-> Fin (m + n)

-- forward direction

finNSum :: SNat m -> SNat n -> Either (FinN m) (FinN n) -> FinN (Plus m n)
finNSum m n (Left (FinN i iLTm))  = FinN (plus i n) (plusMono m iLTm (lteRefl n))
finNSum m _ (Right (FinN j jLTn)) = FinN j (ltePlus m jLTn)

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
finNProd (SS _) n (FinN i iLTm, FinN j jLTn)
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
