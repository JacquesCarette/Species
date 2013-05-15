{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Bag (Bag, empty, singleton, toBag, size, union, elem, find, sum) where

import           Control.Applicative (Applicative)
import qualified Data.List           as L
import           Prelude             hiding (elem, sum)
import qualified Prelude             as P

newtype Bag a = Bag [a]
  deriving (Functor, Applicative, Monad)

empty :: Bag a
empty = toBag []

singleton :: a -> Bag a
singleton a = toBag [a]

toBag :: [a] -> Bag a
toBag = Bag

-- | Proof obligation: the first argument is a function which yields
--   the same result for any permutation of a given input list.
elimBag :: ([a] -> b) -> Bag a -> b
elimBag f (Bag xs) = f xs

size :: Bag a -> Int
size (Bag as) = length as

union :: Bag a -> Bag a -> Bag a
union (Bag as) (Bag bs) = Bag (as ++ bs)

elem :: Eq a => a -> Bag a -> Bool
elem a (Bag as) = a `P.elem` as

find :: (a -> Bool) -> Bag a -> Maybe a
find p (Bag as) = L.find p as

sum :: Num a => Bag a -> a
sum = elimBag P.sum
