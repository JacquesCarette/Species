{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE GADTs                 #-}

module Data.Storage
    ( Storage(..)
    , emptyStorage
    )
    where

import Prelude hiding (zip, zipWith, concat)
import GHC.Exts

import Control.Lens (review,retagged)
import Control.Applicative (liftA2)

import qualified Data.HashMap.Lazy as HM
import Data.HashMap.Lazy ((!))
import Data.Hashable

import Data.Type.Nat
import Data.Fin
import Data.Finite
import Data.Subset

-- | Instances of @Storage@ represent \"memory\" which can be indexed by
--   arbitrary labels.
class Storage s where
  type LabelConstraint s l :: Constraint

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
  replace :: LabelConstraint s l => l -> a -> s l a -> (a, s l a)

  -- | Map over the contents of the storage.
  smap :: (a -> b) -> s l a -> s l b
  -- Ideally we would have a unversally quantified constraint (forall
  -- l. Functor (s l)), but Haskell doesn't let us express that.

  -- | Zip together two storage blocks with the same label type.
  zipWith :: (a -> b -> c) -> s l a -> s l b -> s l c

  -- | Combine two storage blocks into one, taking the disjoint union
  --   of their label types.
  append :: s l1 a -> s l2 a -> s (Either l1 l2) a

  -- | Collapse nested blocks of storage into one, taking the pair of
  --   their label types.
--  concat :: s l1 (s l2 a) -> s (l1,l2) a

  -- | Initialize a potentially infinite block of storage with some
  --   initial content.  This is experimental.
  initialize :: (l -> a) -> s l a
  
-- | A storage block of zero size.
emptyStorage :: Storage s => s (Fin Z) a
emptyStorage = allocate finite_Fin absurd

instance Storage (->) where
  type LabelConstraint (->) l = Eq l
  allocate _ f          = f
  reindex sub f         = f . review (asPIso sub)
  index                 = id
  replace l a f         = (f l, \l' -> if l == l' then a else f l')
  zipWith               = liftA2
  smap                  = (.)
  append f _ (Left l1)  = f l1
  append _ g (Right l2) = g l2
--  concat                = uncurry
  initialize f          = f

{- 
   Comment out this for now, will get back to it later.

-- A HashMap can *almost* be made an instance of Storage, save for a
-- sane way to implement reindex.  And since that is rather crucial,
-- we have to wrap things up so that it can be made to work.
data FinHashMap l v where
   FHM :: (HasSize l, Hashable l, Eq l) => 
               Finite l -> HM.HashMap l v -> FinHashMap l v

-- allocation requires real work.
alloc_fhm :: (HasSize l, Hashable l, Eq l) => Finite l -> (l -> a) -> HM.HashMap l a
alloc_fhm fin f = foldr (\l m -> HM.insert l (f l) m) HM.empty 
    (map (fromFin fin) (fins (size fin)))

-- changing keys is work too.
rekey :: (Hashable l', Eq l') => (l -> l') -> HM.HashMap l a -> HM.HashMap l' a
rekey f m = HM.foldrWithKey (\k v nm -> HM.insert (f k) v nm) HM.empty m

instance Storage FinHashMap where
  type LabelConstraint FinHashMap l = (Eq l, Hashable l, HasSize l)
  allocate fin f                   = FHM fin (alloc_fhm fin f)
{-
  reindex sub (FHM fin h) = FHM (retagged (asPIso sub)) h
-}
  index (FHM fin h) l              = h ! l
  replace l a (FHM fin h)          = (h ! l, FHM fin (HM.insert l a h))
  -- below assumes that both isos are the same.
  -- furthermore, since the maps are total, intersection is total too
  zipWith g (FHM f1 h1) (FHM _ h2) = FHM f1 (HM.intersectionWith g h1 h2)
  smap g (FHM f h)                 = FHM f (HM.map g h)
  append (FHM f1 h1) (FHM f2 h2)   = 
      FHM (finite_Either f1 f2) (HM.union (rekey Left h1) (rekey Right h2))

{-
  initialize h          = h
-}
-}
