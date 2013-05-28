{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeOperators             #-}

module Map (Map, empty, singleton, insert, toMap, remap, mapLabels, relabel', relabel, size, union, lookup) where

import           BFunctor
import           Control.Arrow (first)
import           Control.Lens
import           Data.Maybe    (catMaybes)
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

-- | Modify the labels, and also delete any labels which map to Nothing
remap :: (l -> Maybe l') -> Map l a -> Map l' a
remap f (Map ls) = Map (catMaybes . map (strength . first f) $ ls)
  where strength (fa,b) = fmap (,b) fa

mapLabels :: (l -> l') -> Map l a -> Map l' a
mapLabels = remap . (Just .)

relabel' :: (l <-> l') -> (Map l a <-> Map l' a)
relabel' = liftIso ls ls
  where
    ls = assocs.mapped._1

relabel :: (l <-> l') -> Map l a -> Map l' a
relabel = view . relabel'

size :: Map l a -> Int
size (Map as) = length as

union :: Map l a -> Map l a -> Map l a
union (Map as) (Map bs) = Map (as ++ bs)

lookup :: Eq l => l -> Map l a -> Maybe a
lookup l (Map as) = P.lookup l as
