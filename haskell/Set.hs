{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Set (Set, empty, singleton, insert, toSet, map, size, union, elem, find, sum) where

import           BFunctor
import           Control.Applicative (Applicative)
import qualified Data.List           as L
import           Prelude             hiding (elem, sum, map)
import qualified Prelude             as P

newtype Set a = Set [a]
  deriving (Functor, Applicative, Monad)

instance BFunctor Set

empty :: Set a
empty = Set []

singleton :: a -> Set a
singleton a = Set [a]

insert :: Eq a => a -> Set a -> Set a
insert a (Set as)
  | a `P.elem` as = Set as
  | otherwise   = Set (a:as)

toSet :: Eq a => [a] -> Set a
toSet = Set . L.nub

-- | Proof obligation: the first argument is a function which yields
--   the same result for any permutation of a given input list.
elimSet :: ([a] -> b) -> Set a -> b
elimSet f (Set xs) = f xs

map :: Eq b => (a -> b) -> Set a -> Set b
map f (Set as) = Set (L.nub $ P.map f as)

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
