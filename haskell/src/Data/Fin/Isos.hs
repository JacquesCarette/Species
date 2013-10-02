{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators  #-}

-- | Some isomorphisms of finite sets.
--
--   Note that these isomorphisms have real computational content,
--   specifying canonical mappings which are used to determine indices
--   for storage of data associated to algebraic structures.
module Data.Fin.Isos
    ( -- * Disjoint union of finite sets
      -- $disjoint

      finSum,  finSum', finSumI

      -- * Cartesian product of finite sets

    , finProd, finProd', finProdI
    )
    where

import           Control.Arrow            ((***), (+++))
import           Control.Lens (iso)

import           Data.Iso
import           Data.Fin
import           Data.Type.Equality
import           Data.Type.Nat
import           Data.Type.Nat.Div
import           Data.Type.Nat.Inequality
import           Data.Type.Nat.Minus

------------------------------------------------------------
-- Sum of Fins: Either (Fin m) (Fin n) <-> Fin (m + n)
------------------------------------------------------------

-- XXX TODO: document this better.

-- forward direction

finNSum :: SNat m -> SNat n -> Either (FinN m) (FinN n) -> FinN (Plus m n)
finNSum m n (Left (FinN i iLTm))  = FinN (plus i n) (plusMono m iLTm (lteRefl n))
finNSum m _ (Right (FinN j jLTn)) = FinN j (ltePlus m jLTn)

-- | An isomorphism witnessing that the disjoint union of sets of
--   sizes m and n is a set of size (m + n).  In particular, given
--   sets {0..m-1} and {0..n-1}, it maps @Left i@ to @i@ and @Right j@
--   to @m + j@.
finSum :: SNat m -> SNat n -> Either (Fin m) (Fin n) -> Fin (Plus m n)
finSum m n = case plusComm m n of
               Refl -> finNToFin . finNSum n m . swapEither . (finToFinN +++ finToFinN)

-- backward direction

finNSum' :: SNat m -> SNat n -> FinN (Plus m n) -> Either (FinN m) (FinN n)
finNSum' m n (FinN x xLTmn) =
  case decLT n x of
    Left xLTn -> Right (FinN x xLTn)
    Right (Minus j Refl) -> Left (FinN j (lteCancelPlusR (SS j) m n xLTmn))

finSum' :: SNat m -> SNat n -> Fin (Plus m n) -> Either (Fin m) (Fin n)
finSum' m n = case plusComm m n of
                Refl -> (finNToFin +++ finNToFin) . swapEither . finNSum' n m . finToFinN

swapEither :: Either a b -> Either b a
swapEither (Left a)  = Right a
swapEither (Right b) = Left b

-- iso

finSumI :: SNat m -> SNat n -> (Either (Fin m) (Fin n) <-> Fin (Plus m n))
finSumI m n = iso (finSum m n) (finSum' m n)

--------------------------------------------------
-- Product of Fins: Fin (m * n) <-> (Fin m, Fin n)

-- XXX TODO: document this better.

-- forward direction

finNProd :: SNat m -> SNat n -> (FinN m, FinN n) -> FinN (Times m n)
finNProd SZ     _ (FinN _ iLTZ, _)             = absurdLT iLTZ
finNProd (SS _) n (FinN i iLTm, FinN j jLTn)
    = FinN (j `plus` (i `times` n)) finNProdPf
  where
    finNProdPf = plusMono n jLTn (timesMono n (lteInj iLTm) (lteRefl n))

finProd :: SNat m -> SNat n -> (Fin m, Fin n) -> Fin (Times m n)
finProd m n = finNToFin . finNProd m n . (finToFinN *** finToFinN)

-- backward direction

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

-- iso

finProdI :: SNat m -> SNat n -> ((Fin m, Fin n) <-> Fin (Times m n))
finProdI m n = iso (finProd m n) (finProd' m n)
