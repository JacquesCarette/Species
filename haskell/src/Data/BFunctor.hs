{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE Rank2Types        #-}
{-# LANGUAGE TypeOperators     #-}

module Data.BFunctor where

import Control.Lens
import Data.Finite

-- | Functors in the category B of finite sets with isomorphisms as
--   arrows.
--
--   Note that @bmap@ has a default implementation in terms of 'fmap'
--   for @f@ which are also an instance of @Functor@ (however,
--   not all @BFunctor@s are @Functor@s.)
class BFunctor f where
  bmap :: (Finite a, Finite b) => (a <-> b) -> (f a <-> f b)

  default bmap :: Functor f => (a <-> b) -> (f a <-> f b)
  bmap g = mapping g
