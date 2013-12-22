{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs         #-}

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
fromMS :: Storage s => MS.MultiSet a -> Sp' E s a
fromMS = e' . MS.elems

instance ImpLabelled (MS.MultiSet a) where
  type EltType (MS.MultiSet a) = a
  type ShapeOf (MS.MultiSet a) = E
  elimLabelled          = elimE id
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
--   'foldr'.
elimArbo :: (a -> MS.MultiSet r -> r) -> Elim Arbo a r
elimArbo f =
  mapElimShape (view isoArbo) $
    elimProd (elimX (\a -> elimComp (elimE (f a)) (elimArbo f)))

data SetTree a = SetTree a (MS.MultiSet (SetTree a))

fromSetTree :: Storage s => SetTree a -> Sp' Arbo s a
fromSetTree (SetTree a st) = node a (fromMS (MS.mapMonotonic fromSetTree st))

instance ImpLabelled (SetTree a) where
  type EltType (SetTree a) = a
  type ShapeOf (SetTree a) = Arbo
  elimLabelled             = elimArbo SetTree
  toLabelled               = fromSetTree

{-
------------------------------------------------------------------------------
-- | Haskell HashMap is (essentially) a labelled bag.
--   To make things work though, we really need to package up a Finite l
--   in there.
data FinHashMap l v where
   FHM :: (Data.Hashable.Hashable l, Eq l) => 
               Finite l -> HM.HashMap l v -> FinHashMap l v

fromFM :: (Storage s) => FinHashMap l a -> Sp E s l a
fromFM (FHM fin hm) = e fin (\l -> hm ! l)

instance Labelled (FinHashMap l a) where
  type EltType (FinHashMap l a) = a
  type ShapeOf (FinHashMap l a) = E
  elimLabelled          = elimE id
-}
