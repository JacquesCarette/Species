{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}

-- Total maps.

module TMap (Map, empty, singleton, mapLabels, size, union, unUnion, lookup) where

import           Control.Arrow (first)
import           Data.Maybe    (fromJust)
import           Data.Void
import           Iso
import qualified Prelude       as P
import           Prelude       hiding (lookup)
import qualified Set as S

newtype Map l a = Map [(l,a)]
  deriving (Functor)

empty :: Map Void a
empty = toMap []

singleton :: a -> Map () a
singleton a = toMap [((),a)]

toMap :: [(l,a)] -> Map l a
toMap = Map

-- mkMap :: (l -> a) -> Map l a
-- mkMap

-- | Proof obligation: the first argument is a function which yields
--   the same result for any permutation of a given input list.
elimMap :: ([(l,a)] -> b) -> Map l a -> b
elimMap f (Map xs) = f xs

mapLabels :: (l <-> l') -> Map l a -> Map l' a
mapLabels f (Map ls) = Map ((map . first) (there f) ls)

size :: Map l a -> Int
size (Map as) = length as

union :: Map l1 a -> Map l2 a -> Map (Either l1 l2) a
union (Map as) (Map bs) = Map ((map . first) Left as ++ (map . first) Right bs)

unUnion :: Map (Either l1 l2) a -> (Map l1 a, Map l2 a)
unUnion = undefined -- XXX implement me

lookup :: Eq l => l -> Map l a -> a
lookup l (Map as) = fromJust $ P.lookup l as
  -- fromJust is justified since all maps are total by construction
