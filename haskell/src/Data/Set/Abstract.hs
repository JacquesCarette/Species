{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | A simple model of abstract (mathematical) sets.
module Data.Set.Abstract (Set, enumerate, elimSet, emptySet, union) where

import           Control.Lens
import           Data.BFunctor
import           Data.Fin
import           Data.Finite

-- | A set is an unordered collection of elements in which each
--   element occurs at most once.
newtype Set a = Set [a]
  deriving Show

instance BFunctor Set where
  bmap i = iso (\(Set as) -> Set (map (view i) as))
               (\(Set as) -> Set (map (view (from i)) as))

-- | The set of elements of a 'Finite' type.
enumerate :: forall l. Finite l -> Set l
enumerate f@(F finite) = Set $ map (view finite) (fins (size f))

-- | The empty set
emptySet = Set []

-- | Union
union :: Set a -> Set b -> Set (Either a b)
union (Set la) (Set lb) = Set (map Left la ++ map Right lb)

-- | Generic eliminator for 'Set'. Note that using @elimSet@ incurs a
--   proof obligation, namely, the first argument must be a function
--   which yields the same result for any permutation of a given input
--   list.
elimSet :: ([a] -> b) -> Set a -> b
elimSet f (Set xs) = f xs
