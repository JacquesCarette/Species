{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}

-- | Another example.

module Data.Species.Rose
    ( -- * Rose tree structures

      Rose(..), isoRose

      -- * Introduction forms

    , rose_, rose, node, fromRose

      -- * Eliminator

    , elimRose, toRose, toRose'

    )
    where

import           Control.Lens       (Iso, from, iso, view)
import           Data.Functor       ((<$>))
import           Data.Tree

import           Data.BFunctor
import           Data.Iso (liftIso)
import           Data.Species.Convert
import           Data.Species.Elim
import           Data.Species.List
import           Data.Species.Shape
import           Data.Species.Types
import           Data.Storage

-- | @Rose@ represents the shape of (finite) rose trees. It is defined
--   directly according to the recurrence @Rose = X * (L o Rose)@.
newtype Rose l = Rose { unRose :: (X * (Comp L Rose)) l }

-- | An isomorphism to mediate unfolding and refolding @Rose@-structures
--   one step.
isoRose :: Iso (Rose l) (Rose l') ((X*(Comp L Rose)) l) ((X*(Comp L Rose)) l')
isoRose = iso unRose Rose

instance BFunctor Rose where
  bmap g = liftIso isoRose isoRose (bmap g)

-- | Introduce a rose tree shape.
rose_ :: (X*(Comp L Rose)) l -> Rose l
rose_ = view (from isoRose)

-- | Introduce a list structure.
rose :: Eq l => Sp (X*(Comp L Rose)) s l a -> Sp Rose s l a
rose = reshape (view (from isoRose))

rose' :: Sp' (X*(Comp L Rose)) s a -> Sp' Rose s a
rose' sp' = case sp' of SpEx sp -> SpEx (rose sp)

node :: Storage s => a -> [Sp' Rose s a] -> Sp' Rose s a
node a ts = rose' $ prod' (x' a) (compJ'' (fromList ts))

-- | Convert a Haskell rose tree to a labelled rose tree structure.
fromRose :: Storage s => Tree a -> Sp' Rose s a
fromRose (Node a ts) = node a (map fromRose ts)

-- | An eliminator for labelled list structures, the equivalent of
--   'foldr'.
elimRose :: (a -> [r] -> r) -> Elim Rose a r
elimRose f =
  mapElimShape (view isoRose) $
    elimProd (elimX (\a -> elimComp (f a <$> elimList [] (:)) (elimRose f)))

toRose :: (Eq l, Storage s) => Sp Rose s l a -> Tree a
toRose = fromLabelled

toRose' :: Sp' Rose s a -> Tree a
toRose' = fromLabelled'

instance Labelled (Tree a) where
  type EltType (Tree a) = a
  type ShapeOf (Tree a) = Rose
  toLabelled            = fromRose
  elimLabelled          = elimRose Node

