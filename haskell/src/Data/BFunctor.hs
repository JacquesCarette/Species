{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE Rank2Types        #-}
{-# LANGUAGE TypeOperators     #-}

module Data.BFunctor where

import Control.Lens
import Data.Finite

-- Functors in the category B of finite sets with isomorphisms as
-- arrows.
class BFunctor f where
  bmap :: (Finite a, Finite b) => (a <-> b) -> (f a <-> f b)

  -- Any Functor is automatically a BFunctor. (However, some things
  -- are BFunctors but not Functors.)
  default bmap :: Functor f => (a <-> b) -> (f a <-> f b)
  bmap g = mapping g
