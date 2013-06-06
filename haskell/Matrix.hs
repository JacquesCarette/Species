
module Matrix where

import Nat
import SpeciesTypes

type MatrixSh = Comp E E

type Matrix m n = Sp MatrixSh (Fin m, Fin n)

mkMatrix :: (Natural m, Natural n)
         => (Fin m -> Fin n -> a) -> Matrix m n a
mkMatrix m = compA (e m) (e id)

transpose :: (Natural m, Natural n)
          => Matrix m n a -> Matrix n m a
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
