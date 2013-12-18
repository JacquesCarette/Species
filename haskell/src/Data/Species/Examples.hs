{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}

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

------------------------------------------------------------------------------

-- | Haskell MultiSet is a Bag
fromMS :: Storage s => MS.MultiSet a -> Sp' E s a
fromMS = e' . MS.elems

instance Labelled (MS.MultiSet a) where
  type EltType (MS.MultiSet a) = a
  type ShapeOf (MS.MultiSet a) = E
  toLabelled            = fromMS
  elimLabelled          = undefined -- TODO

------------------------------------------------------------------------------

-- | Much like Rose trees, general trees use a set rather than a list
-- of sub-trees.
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

{-
-- | Convert a Haskell tree to a labelled rose tree structure.
fromRose :: Storage s => Tree a -> Sp' Rose s a
fromRose (Node a ts) = node a (map fromRose ts)
-}

{-  TODO: need elimE
-- | An eliminator for labelled general tree structures, the equivalent of
--   'foldr'.
elimArbo :: (a -> E r -> r) -> Elim Arbo a r
elimArbo f =
  mapElimShape (view isoArbo) $
    elimProd (elimX (\a -> elimComp (elimE (f a)) (elimArbo f)))
-}

{-
toRose :: (Eq l, Storage s) => Sp Rose s l a -> Tree a
toRose = fromLabelled

toRose' :: Sp' Rose s a -> Tree a
toRose' = fromLabelled'

instance Labelled (Tree a) where
  type EltType (Tree a) = a
  type ShapeOf (Tree a) = Rose
  toLabelled            = fromRose
  elimLabelled          = elimRose Node
-}