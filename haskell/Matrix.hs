{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Matrix where

import ArithIsos
import Data.List (foldl')
import FinIsos
import Finite
import Nat
import Proxy
import Set
import SpeciesTypes
import Vec hiding (enumerate)
import Zippy

type MatrixSh = E

joinE' :: Comp E E --> E
joinE' (Comp _ _ _ _) = E enumerate

joinE :: Finite l => Sp (Comp E E) l a -> Sp E l a
joinE = reshape joinE'

splitE :: forall l1 l2 a. (Finite l1, Finite l2) => Sp E (l1,l2) a -> Sp E l1 (Sp E l2 a)
splitE (Struct _ as) = Struct eSh (mkV l1Sz $ \i ->
                         Struct eSh (mkV l2Sz $ \j ->
                           vIndex as (finPair l1Sz l2Sz (i, j))
                         )
                       )
  where
    l1Sz = size (Proxy :: Proxy l1)
    l2Sz = size (Proxy :: Proxy l2)

type Matrix2 m n = Sp MatrixSh (Fin m, Fin n)

mkMatrix2 :: (Natural m, Natural n)
         => (Fin m -> Fin n -> a) -> Matrix2 m n a
mkMatrix2 m = joinE $ compA (e m) (e id)

transpose :: (Natural m, Natural n)
          => Matrix2 m n a -> Matrix2 n m a
transpose = relabel commT

sum2 :: Num a => Matrix2 m n a -> Matrix2 m n a -> Matrix2 m n a
sum2 = zipWithS (+)

elimE :: Finite l => (a -> a -> a) -> a -> Sp E l a -> a
elimE op e = (elim . Elim) (\(Shape (E s)) m -> elimSet (foldl' op e . map m) s)

prod2' :: (Natural m, Natural n, Natural p)
       => (a -> a -> a) -> a -> (a -> a -> a)
       -> Matrix2 m p a -> Matrix2 p n a -> Matrix2 m n a
prod2' s e p m1 m2
  = joinE
  . fmap (elimE s e . uncurry (zipWithS p))
  $ compAP (splitE m1) (splitE (transpose m2))

prod2 :: (Num a, Natural m, Natural n, Natural p)
      => Matrix2 m p a -> Matrix2 p n a -> Matrix2 m n a
prod2 = prod2' (+) 0 (*)

{-

   It works!!  Squaring the matrix [[0 1] [1 2]] in GHCi:

>>> let m = mkMatrix2 (fin finToInt ((+1) .)) :: Matrix2 (S (S Z)) (S (S Z)) Int
>>> m
Struct {_shape = Shape {_shapeVal = E (Set [(FZ,FZ),(FZ,FS FZ),(FS FZ,FZ),(FS FZ,FS FZ)])}, _elts = VCons 0 (VCons 1 (VCons 1 (VCons 2 VNil)))}
>>> prod2 m m
Struct {_shape = Shape {_shapeVal = E (Set [(FZ,FZ),(FZ,FS FZ),(FS FZ,FZ),(FS FZ,FS FZ)])}, _elts = VCons 1 (VCons 2 (VCons 2 (VCons 5 VNil)))}

-}

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
