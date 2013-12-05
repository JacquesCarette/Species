{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators         #-}

module Data.Storage
    ( Storage(..)
    , emptyStorage
    , AppendStorage(..)
    )
    where

import Prelude hiding (zip, zipWith, concat)

import Control.Lens (review)
import Control.Applicative (liftA2)

import Data.Type.Nat
import Data.Fin
import Data.Finite
import Data.Subset

-- Note, we have Storage s l instead of just Storage s so that (1) we
-- can express the Functor (s l) constraint, and (2) instances can put
-- constraints on l, e.g. a Map-based instance might need an Ord
-- constraint.

-- | Instances of @Storage@ represent \"memory\" which can be indexed by
--   arbitrary labels.
class Functor (s l) => Storage s l where

  -- | Allocate a finite block of storage with some initial content.
  allocate :: Finite l -> (l -> a) -> s l a

  -- | Reindex a block of storage.  Note that the new label type can
  --   be a /subset/ of the old---in that case data corresponding to
  --   the remaining labels will simply be inaccessible.  However,
  --   isomorphisms @(l' <-> l)@ are a valid subtype of @(l' ⊆ l)@;
  --   passing in an isomorphism will simply do a relabeling.
  reindex  :: (l' ⊆ l) -> s l a -> s l' a

  -- | Index into the storage, returning the value associated to a
  -- given label.
  index  :: s l a -> l -> a

  -- | Replace the value associated to a given label, returning the
  --   old value and the updated storage.
  replace :: l -> a -> s l a -> (a, s l a)

  -- | Zip together two storage blocks with the same label type.
  zipWith :: (a -> b -> c) -> s l a -> s l b -> s l c

-- | A storage block of zero size.
emptyStorage :: Storage s (Fin Z) => s (Fin Z) a
emptyStorage = allocate finite_Fin absurd

class AppendStorage s l1 l2 where

  -- | Combine two storage blocks into one, taking the disjoint union
  --   of their label types.
  append :: s l1 a -> s l2 a -> s (Either l1 l2) a

  -- | Collapse nested blocks of storage into one, taking the pair of
  --   their label types.
  concat :: s l1 (s l2 a) -> s (l1,l2) a

instance Eq l => Storage (->) l where
  allocate _ f          = f
  reindex sub f         = f . review (asPIso sub)
  index                 = id
  replace l a f         = (f l, \l' -> if l == l' then a else f l')
  zipWith               = liftA2

instance AppendStorage (->) l1 l2 where
  append f _ (Left l1)  = f l1
  append _ g (Right l2) = g l2
  concat                = uncurry
