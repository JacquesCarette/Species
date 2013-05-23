{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Set (Set, empty, singleton, toSet, size, union, elem, find, sum) where

import           BFunctor
import           Control.Applicative (Applicative)
import qualified Data.List           as L
import           Prelude             hiding (elem, sum)
import qualified Prelude             as P

newtype Set a = Set [a]
  deriving (Functor, Applicative, Monad)

instance BFunctor Set

empty :: Set a
empty = Set []

singleton :: a -> Set a
singleton a = Set [a]

toSet :: Eq a => [a] -> Set a
toSet = Set . L.nub

-- | Proof obligation: the first argument is a function which yields
--   the same result for any permutation of a given input list.
elimSet :: ([a] -> b) -> Set a -> b
elimSet f (Set xs) = f xs

size :: Set a -> Int
size (Set as) = length as

union :: Eq a => Set a -> Set a -> Set a
union (Set as) (Set bs) = Set (L.nub $ as ++ bs)

elem :: Eq a => a -> Set a -> Bool
elem a (Set as) = a `P.elem` as

find :: (a -> Bool) -> Set a -> Maybe a
find p (Set as) = L.find p as

sum :: Num a => Set a -> a
sum = elimSet P.sum
