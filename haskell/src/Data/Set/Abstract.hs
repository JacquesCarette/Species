{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Set.Abstract (Set, enumerate, elimSet) where

import           Control.Lens
import           Data.BFunctor
import           Data.Fin
import           Data.Finite
import           Data.Proxy

newtype Set a = Set [a]
  deriving Show

instance BFunctor Set where
  bmap i = iso (\(Set as) -> Set (map (view i) as))
               (\(Set as) -> Set (map (view (from i)) as))

enumerate :: forall l. Finite l => Set l
enumerate = Set $ map (view finite) (fins (size (Proxy :: Proxy l)))

-- | Proof obligation: the first argument is a function which yields
--   the same result for any permutation of a given input list.
elimSet :: ([a] -> b) -> Set a -> b
elimSet f (Set xs) = f xs
