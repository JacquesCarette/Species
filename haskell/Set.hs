{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Set (Set, empty, singleton, insert, mapInj, size, union, elem, find, sum) where

import           BFunctor
import           Control.Applicative (Applicative)
import qualified Data.List           as L
import           Nat
import           Prelude             hiding (elem, sum, map)
import qualified Prelude             as P

data Set :: Nat -> * -> * where
  Set :: SNat n -> [a] -> Set n a

deriving instance Functor (Set n)

instance BFunctor (Set n)

empty :: Set Z a
empty = Set SZ []

singleton :: a -> Set (S Z) a
singleton a = Set (SS SZ) [a]

-- | Prerequisite: new element is distinct from the existing elements
--   in the set
insert :: a -> Set n a -> Set (S n) a
insert a (Set n as) = Set (SS n) (a:as)

-- | Proof obligation: the first argument is a function which yields
--   the same result for any permutation of a given input list.
elimSet :: ([a] -> b) -> Set n a -> b
elimSet f (Set _ xs) = f xs

-- | Map an /injective/ function over a set.
mapInj :: Eq b => (a -> b) -> Set n a -> Set n b
mapInj f (Set n as) = Set n (P.map f as)

size :: Set n a -> Int
size (Set n as) = snatToInt n

-- | Take the disjoint union of two sets.
union :: Eq a => Set m a -> Set n a -> Set (Plus m n) a
union (Set m as) (Set n bs) = Set (plus m n) (as ++ bs)

elem :: Eq a => a -> Set n a -> Bool
elem a (Set _ as) = a `P.elem` as

find :: (a -> Bool) -> Set n a -> Maybe a
find p (Set _ as) = L.find p as

sum :: Num a => Set n a -> a
sum = elimSet P.sum
