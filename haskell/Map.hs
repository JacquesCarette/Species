{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFunctor #-}

module Map (Map, empty, singleton, insert, toMap, mapLabels, size, union, lookup) where

import           BFunctor
import           Control.Arrow (first)
import           Control.Lens
import qualified Prelude       as P
import           Prelude       hiding (lookup)
import qualified Set           as S

newtype Map l a = Map { _assocs :: [(l,a)] }
  deriving (Functor)

makeLenses ''Map

empty :: Map l a
empty = toMap []

singleton :: l -> a -> Map l a
singleton l a = toMap [(l,a)]

insert :: l -> a -> Map l a -> Map l a
insert l a = union (singleton l a)

toMap :: [(l,a)] -> Map l a
toMap = Map

-- | Proof obligation: the first argument is a function which yields
--   the same result for any permutation of a given input list.
elimMap :: ([(l,a)] -> b) -> Map l a -> b
elimMap f (Map xs) = f xs

mapLabels :: (l -> l') -> Map l a -> Map l' a
mapLabels f (Map ls) = Map ((map . first) f ls)

relabel :: (l <-> l') -> (Map l a <-> Map l' a)
relabel = liftIso ls ls
  where
    ls = assocs.mapped._1

size :: Map l a -> Int
size (Map as) = length as

union :: Map l a -> Map l a -> Map l a
union (Map as) (Map bs) = Map (as ++ bs)

lookup :: Eq l => l -> Map l a -> Maybe a
lookup l (Map as) = P.lookup l as
