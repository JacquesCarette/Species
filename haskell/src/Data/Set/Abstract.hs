{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | A simple model of abstract (mathematical) sets.
module Data.Set.Abstract (Set, enumerate, elimSet) where

import           Control.Lens
import           Data.BFunctor
import           Data.Fin
import           Data.Finite
import           Data.Proxy

-- | A set is an unordered collection of elements in which each
--   element occurs at most once.
newtype Set a = Set [a]
  deriving Show

instance BFunctor Set where
  bmap i = iso (\(Set as) -> Set (map (view i) as))
               (\(Set as) -> Set (map (view (from i)) as))

-- | The set of elements of a 'Finite' type.
enumerate :: forall l. Finite l -> Set l
enumerate (F finite) = Set $ map (view finite) (fins (size (Proxy :: Proxy l)))

-- | Generic eliminator for 'Set'. Note that using @elimSet@ incurs a
--   proof obligation, namely, the first argument must be a function
--   which yields the same result for any permutation of a given input
--   list.
elimSet :: ([a] -> b) -> Set a -> b
elimSet f (Set xs) = f xs
