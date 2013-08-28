{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators  #-}

-- | Some isomorphisms of finite sets.  Each comes as an inverse pair
--   of functions, in both a version on 'Fin' and a version on 'FinN'.
--
--   Note that these isomorphisms have real computational content,
--   specifying canonical mappings which are used to determine indices
--   for storage of data associated to algebraic structures.
module Data.Fin.Isos
    ( -- * Disjoint union of finite sets
      -- $disjoint

      finNSum, finNSum'
    , finSum,  finSum'

      -- * Cartesian product of finite sets

    , finNProd, finNProd'
    , finProd, finProd'
    )
    where

import           Control.Arrow            ((***), (+++))

import           Data.Fin
import           Data.Type.Equality
import           Data.Type.Nat
import           Data.Type.Nat.Div
import           Data.Type.Nat.Inequality
import           Data.Type.Nat.Minus

------------------------------------------------------------
-- Sum of Fins: Either (Fin m) (Fin n) <-> Fin (m + n)
------------------------------------------------------------

-- forward direction

finNSum :: SNat m -> SNat n -> Either (FinN m) (FinN n) -> FinN (Plus m n)
finNSum m n (Left (FinN i iLTm))  = FinN (plus i n) (plusMono m iLTm (lteRefl n))
finNSum m _ (Right (FinN j jLTn)) = FinN j (ltePlus m jLTn)

finSum :: SNat m -> SNat n -> Either (Fin m) (Fin n) -> Fin (Plus m n)
finSum m n = finNToFin . finNSum m n . (finToFinN +++ finToFinN)

-- backward direction

finNSum' :: SNat m -> SNat n -> FinN (Plus m n) -> Either (FinN m) (FinN n)
finNSum' m n (FinN x xLTmn) =
  case decLT n x of
    Left xLTn -> Right (FinN x xLTn)
    Right (Minus j Refl) -> Left (FinN j (lteCancelPlusR (SS j) m n xLTmn))

finSum' :: SNat m -> SNat n -> Fin (Plus m n) -> Either (Fin m) (Fin n)
finSum' m n = (finNToFin +++ finNToFin) . finNSum' m n . finToFinN

--------------------------------------------------
-- Product of Fins: Fin (m * n) <-> (Fin m, Fin n)

-- forward direction

finNProd :: SNat m -> SNat n -> (FinN m, FinN n) -> FinN (Times m n)
finNProd SZ     _ (FinN _ iLTZ, _)             = absurdLT iLTZ
finNProd (SS _) n (FinN i iLTm, FinN j jLTn)
    = FinN (j `plus` (i `times` n)) finNProdPf
  where
    finNProdPf = plusMono n jLTn (timesMono n (lteInj iLTm) (lteRefl n))

finProd :: SNat m -> SNat n -> (Fin m, Fin n) -> Fin (Times m n)
finProd m n = finNToFin . finNProd m n . (finToFinN *** finToFinN)

finNProd' :: SNat m -> SNat n -> FinN (Times m n) -> (FinN m, FinN n)
finNProd' m n (FinN x xlt) = case divisionAlg x n of
  Div i j jlt Refl ->
    ( FinN i (ltCancelMulR i m n
               (lte_ltTrans
                 (ltePlus j (lteRefl (times i n)))
                 xlt
               )
             )
    , FinN j jlt
    )

finProd' :: SNat m -> SNat n -> Fin (Times m n) -> (Fin m, Fin n)
finProd' m n = (finNToFin *** finNToFin) . finNProd' m n . finToFinN
