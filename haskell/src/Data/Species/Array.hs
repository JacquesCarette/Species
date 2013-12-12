{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

-- | This module demonstrates computations with generalized arrays as
--   an example application.
module Data.Species.Array where

import           Data.List            (foldl')
import           Data.Proxy

import           Data.Fin
import           Data.Fin.Isos
import           Data.Finite
import           Data.Set.Abstract
import           Data.Species.Elim
import           Data.Species.Shape
import           Data.Species.Shuffle
import           Data.Species.Types
import           Data.Species.Zippy
import           Data.Type.Isos
import           Data.Type.Nat
import qualified Data.Vec             as V

-- | Typically, we think of an array as an unstructured collection of
--   elements.  If there is any structure it resides in the labels.
type ArraySh = E

-- | Given a bag structure with product labels, we may \"split\" it
--   into a bag of bags.
splitE :: forall l1 l2 s a. (HasSize l1, HasSize l2) => Sp E s (l1,l2) a -> Sp E s l1 (Sp E s l2 a)
splitE (Struct _ as) = Struct e_ (V.mkV l1Sz $ \i ->
                               Struct (e_ finl2) (V.mkV l2Sz $ \j ->
                                 V.index as (finProd l1Sz l2Sz (i, j))
                               ) finl2
                             ) finl1
  where
    finl1 :: Finite l1
    finl2 :: Finite l2
    (finl1,finl2) = undefined -- XXX this is impossible. See below.
    l1Sz = size finl1
    l2Sz = size finl2

-- Really unsure about what to do with splitE.  We could just require
-- the user to pass in Finite proofs for l1 and l2, but that would
-- result in a lot of data shuffling.  It would be much nicer if we
-- had a nice story for doing things in-place as much as possible.  In
-- any case, implementing a function of type Finite (l1,l2) -> (Finite
-- l1, Finite l2) is a non-starter.

-- | An @m x n@ array has labels which are pairs of type @(Fin m, Fin n)@.
type Array2 s m n = Sp ArraySh s (Fin m, Fin n)

-- | Introduction form for 2D arrays, taking a function specifying the
--   array content.
mkArray2 :: (Natural m, Natural n)
         => (Fin m -> Fin n -> a) -> Array2 s m n a
mkArray2 m = forgetShape $ compA (e finite_Fin m) (e finite_Fin id)

-- | Transposition is a simple relabelling.
transpose :: (Natural m, Natural n)
          => Array2 s m n a -> Array2 s n m a
transpose = relabel commT

-- | Sum two arrays elementwise.
sumArray :: (Num a, HasSize l) => Sp ArraySh s l a -> Sp ArraySh s l a -> Sp ArraySh s l a
sumArray = zipWithS (+)

-- | A generic eliminator for bag structures, taking a commutative,
--   associative binary operator and a default value.
elimE :: Eq l => (a -> a -> a) -> a -> Sp E s l a -> a
elimE op z = (elim . Elim) (\(E s) m -> elimSet (foldl' op z . map m) s)

-- | Generalized product of 2D arrays.  The first two arguments define
--   the additive structure (a commutative, associative binary
--   operation and its identity) and the second argument defines a
--   multiplicative structure.
prod2' :: (Natural m, Natural n, Natural p)
       => (a -> a -> a) -> a -> (a -> a -> a)
       -> Array2 s m p a -> Array2 s p n a -> Array2 s m n a
prod2' s z t m1 m2
  = forgetShape
  . fmap (elimE s z . uncurry (zipWithS t))
  $ compAP (splitE m1) (splitE (transpose m2))

-- | The usual product of 2D matrices.
prod2 :: (Num a, Natural m, Natural n, Natural p)
      => Array2 s m p a -> Array2 s p n a -> Array2 s m n a
prod2 = prod2' (+) 0 (*)

{-

   It works!!  Squaring the matrix [[0 1] [1 2]] in GHCi:

>>> let m = mkArray2 (fin finToInt ((+1) .)) :: Array2 (S (S Z)) (S (S Z)) Int
>>> m
Struct {_shape = E (Set [(FZ,FZ),(FZ,FS FZ),(FS FZ,FZ),(FS FZ,FS FZ)]), _elts = VCons 0 (VCons 1 (VCons 1 (VCons 2 VNil)))}
>>> prod2 m m
Struct {_shape = E (Set [(FZ,FZ),(FZ,FS FZ),(FS FZ,FZ),(FS FZ,FS FZ)]}, _elts = VCons 1 (VCons 2 (VCons 2 (VCons 5 VNil)))}

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
