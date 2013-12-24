{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE RankNTypes    #-}

-- | A collection of examples of Species

module Data.Species.Examples where

import           Control.Lens       (Iso, from, iso, view)
import           Data.Functor       ((<$>))
import qualified Data.MultiSet    as MS

import           Data.BFunctor
import           Data.Iso (liftIso)
import           Data.Species.Convert
import           Data.Species.Elim
import           Data.Species.List
import           Data.Species.Shape
import           Data.Species.Types
import           Data.Storage
import           Data.Finite
import           Data.Hashable
import qualified Data.Set.Abstract as S
import qualified Data.HashMap.Lazy as HM
import           Data.HashMap.Lazy ((!))

------------------------------------------------------------------------------

-- | Haskell MultiSet is an unlabelled Bag
--   Note in particular how in the eliminator call we ignore the label.
fromMS :: Storage s => MS.MultiSet a -> Sp' E s a
fromMS = e' . MS.elems

instance ImpLabelled (MS.MultiSet a) where
  type EltType (MS.MultiSet a) = a
  type ShapeOf (MS.MultiSet a) = E
  elimLabelled          = elimE (MS.mapMonotonic snd)
  toLabelled            = fromMS

toMS :: (Eq l, Storage s) => Sp E s l a -> MS.MultiSet a
toMS = fromLabelled

toMS' :: (Storage s) => Sp' E s a -> MS.MultiSet a
toMS' = fromLabelled'

------------------------------------------------------------------------------

-- | Much like Rose trees, rooted (multi-arity) trees use a set rather than 
--   a list of sub-trees.  Since terminology between combinatorics and PL
--   conflicts, we'll stick with 'Arbo' (from the French arborescence) instead
--   of trying to invent some tree variant (as it would be misunderstood 
--   almost surely anyways).
newtype Arbo l = Arbo {unArbo :: (X * (Comp E Arbo)) l }

-- | fold and unfold.  This is so systematic, it should be automated.
isoArbo :: Iso (Arbo l) (Arbo l') ((X*(Comp E Arbo)) l) ((X*(Comp E Arbo)) l')
isoArbo = iso unArbo Arbo

instance BFunctor Arbo where
  bmap g = liftIso isoArbo isoArbo (bmap g)

-- | Introduce a general tree shape.
arbo_ :: (X*(Comp E Arbo)) l -> Arbo l
arbo_ = view (from isoArbo)

-- | Introduce a general tree structure.
arbo :: Eq l => Sp (X*(Comp E Arbo)) s l a -> Sp Arbo s l a
arbo = reshape (view (from isoArbo))

-- | And its existantially quantified form
arbo' :: Sp' (X*(Comp E Arbo)) s a -> Sp' Arbo s a
arbo' sp' = case sp' of SpEx sp -> SpEx (arbo sp)

node :: Storage s => a -> Sp' E s (Sp' Arbo s a) -> Sp' Arbo s a
node a ts = arbo' $ prod' (x' a) (compJ'' ts)

-- | An eliminator for labelled general tree structures, the equivalent of
--   'foldr'.  Explicitly polymorphic on the labels.
elimArbo :: (forall l1. a -> MS.MultiSet (l1, r) -> r) -> Elim Arbo l a r
elimArbo f =
  mapElimShape (view isoArbo) $
    elimProd (const $ elimX (\a -> elimComp (elimE (f a)) (elimArbo f)))

data SetTree a = SetTree a (MS.MultiSet (SetTree a))

fromSetTree :: Storage s => SetTree a -> Sp' Arbo s a
fromSetTree (SetTree a st) = node a (fromMS (MS.mapMonotonic fromSetTree st))

instance ImpLabelled (SetTree a) where
  type EltType (SetTree a) = a
  type ShapeOf (SetTree a) = Arbo
  elimLabelled             = elimArbo (\a ms -> SetTree a (MS.mapMonotonic snd ms))
  toLabelled               = fromSetTree

------------------------------------------------------------------------------
-- | Haskell HashMap is (essentially) a labelled bag (with Hashable labels)
--   To make things work though, we really need to package up a Finite l
--   in our data-structure, and ask for it when needed.
data FinHashMap l v where
   FHM :: (Hashable l, Eq l) => Finite l -> HM.HashMap l v -> FinHashMap l v

fromFHM :: (Storage s) => FinHashMap l a -> Sp E s l a
fromFHM (FHM fin hm) = e fin (\l -> hm ! l)

toFHM :: (Eq l, Hashable l, Storage s) => Finite l -> Sp E s l a -> FinHashMap l a
toFHM finl s = elim (elimExpLabelled finl) s

instance (Hashable l, Eq l) => ExpLabelled (FinHashMap l a) where
  type EltLT     (FinHashMap l a) = a
  type ShapeOfLT (FinHashMap l a) = E
  type LabelType (FinHashMap l a) = l
  toExpLabelled                   = fromFHM
  elimExpLabelled pf              = elimE f 
    where f ms = FHM pf (MS.fold (\(l,x) hm -> HM.insert l x hm) HM.empty ms)
