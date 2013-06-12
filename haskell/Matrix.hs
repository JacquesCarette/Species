{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Matrix where

import ArithIsos
import Finite
import Nat
import Proxy
import Set
import SpeciesTypes
import Vec hiding (enumerate)

type MatrixSh = E

joinE :: Comp E E --> E
joinE (Comp _ _ _ _) = E enumerate

splitE :: forall l1 l2 a. (Finite l1, Finite l2) => Sp E (l1,l2) a -> Sp E l1 (Sp E l2 a)
splitE (Struct _ as) = Struct eSh (mkV l1Sz $ \i ->
                         Struct eSh (mkV l2Sz $ \j ->
                           vIndex as (finPair l1Sz i j)
                         )
                       )
  where
    l1Sz = size (Proxy :: Proxy l1)
    l2Sz = size (Proxy :: Proxy l2)

type Matrix2 m n = Sp MatrixSh (Fin m, Fin n)

mkMatrix2 :: (Natural m, Natural n)
         => (Fin m -> Fin n -> a) -> Matrix2 m n a
mkMatrix2 m = reshape joinE $ compA (e m) (e id)

transpose :: (Natural m, Natural n)
          => Matrix2 m n a -> Matrix2 n m a
transpose = relabel commT




{-

-- an old (currently aborted) attempt at converting from Haskell
-- Arrays, but that's hard

-- Array -----------------------------------------

-- Arrays are finite maps, i.e. labelled bags.  We keep the original
-- index range around so we can convert back later, since the type i
-- is not required to be isomorphic to the set of labels.

data Arr i l = Arr (i,i) (E l)

-- It would be nicer if we could get an explicit label type out, but
-- the problem is that the type i doesn't really tell us much: Arrays
-- can (and typically do) use only a subset of the index type for
-- their indices.  It would be nice if Haskell had some sort of
-- subset/range types.
fromArray :: Ix i => Array i e -> Sp' (Arr i) e
fromArray arr = undefined
  where
    (lo,hi) = bounds arr
    sz      = rangeSize (lo,hi)
-}
