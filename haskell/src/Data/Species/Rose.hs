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
import           Data.Finite
import           Data.Species.Convert
import           Data.Species.Elim
import           Data.Species.List
import           Data.Species.Shape
import           Data.Species.Types

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
rose_ :: Finite l => (X*(Comp L Rose)) l -> Rose l
rose_ = view (from isoRose)

-- | Introduce a list structure.
rose :: Finite l => Sp (X*(Comp L Rose)) l a -> Sp Rose l a
rose = reshape (view (from isoRose))

rose' :: Sp' (X*(Comp L Rose)) a -> Sp' Rose a
rose' sp' = case sp' of SpEx sp -> SpEx (rose sp)

node :: a -> [Sp' Rose a] -> Sp' Rose a
node a ts = rose' $ prod' (x' a) (compJ'' (fromList ts))

-- | Convert a Haskell rose tree to a labelled rose tree structure.
fromRose :: Tree a -> Sp' Rose a
fromRose (Node a ts) = node a (map fromRose ts)

-- | An eliminator for labelled list structures, the equivalent of
--   'foldr'.
elimRose :: (a -> [r] -> r) -> Elim Rose a r
elimRose f =
  mapElimShape (view isoRose) $
    elimProd (elimX (\a -> elimComp (f a <$> elimList [] (:)) (elimRose f)))

toRose :: Finite l => Sp Rose l a -> Tree a
toRose = fromLabelled

toRose' :: Sp' Rose a -> Tree a
toRose' = fromLabelled'

instance Labelled (Tree a) where
  type EltType (Tree a) = a
  type ShapeOf (Tree a) = Rose
  toLabelled            = fromRose
  elimLabelled          = elimRose Node

{-

Unfortunately it seems we have a bug:

>>> let t = Node 3 [Node 4 [], Node 5 []] :: Tree Int
>>> toRose' (fromRose t)
Node {rootLabel = 5, subForest = [Node {rootLabel = 3, subForest = []},Node {rootLabel = 4, subForest = []}]}

This just goes to show that it really does matter *which* isomorphisms
we choose!

-}
