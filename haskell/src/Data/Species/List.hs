{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | An example showing how to build up more complex (possibly recursive)
--   structures.

module Data.Species.List
    ( -- * List structures

      L(..), isoL

      -- * Introduction forms

    , list_, list, nil, cons, fromList

      -- * Eliminator

    , elimList

    )
    where

import           Control.Lens       (Iso, from, iso, view)

import           Data.BFunctor
import           Data.Fin
import           Data.Finite
import           Data.Species.Elim
import           Data.Species.Shape
import           Data.Species.Types
import           Data.Type.Nat
import qualified Data.Vec           as V

-- | @L@ represents the shape of (finite) lists. It is defined
--   directly according to the recurrence @L = One + X * L@.
newtype L l = L { unL :: (One + X * L) l }

-- | An isomorphism to mediate unfolding and refolding @L@-structures
--   one step.  Intuitively, you can think of this as having a type like
--
--   @
--   L l \<-\> (One + X*L) l
--   @
--
--   The extra complication is to allow the use of the isomorphism in
--   transformations which change the type of the labels.
isoL :: Iso (L l) (L l') ((One + X*L) l) ((One + X*L) l')
isoL = iso unL L

instance BFunctor L where
  bmap g = liftIso isoL isoL (bmap g)

-- Some introduction forms for lists, and an example of converting a
-- Haskell list to a Sp' L.  Ideally all of this would be generically
-- derivable.

-- | Introduce a list shape.
list_ :: Finite l => (One + X*L) l -> L l
list_ = view (from isoL)

-- | Introduce a list structure.
list :: Finite l => Sp (One + X*L) l a -> Sp L l a
list = reshape (view (from isoL))

-- | The empty list structure.
nil :: Sp L (Fin Z) a
nil = list $ inl one

-- | Cons for list structures.
cons :: (Eq l, Finite l) => a -> Sp L l a -> Sp L (Either (Fin (S Z)) l) a
cons a (Struct shp es) = Struct (list_ (inr_ (prod_ x_ shp))) (V.VCons a es)

-- | Convert a Haskell list to a labelled list structure.
fromList :: [a] -> Sp' L a
fromList [] = SpEx nil
fromList (a:as) =
  case fromList as of
    SpEx s -> SpEx (cons a s)

-- | An eliminator for labelled list structures, the equivalent of
--   'foldr'.
elimList :: r -> (a -> r -> r) -> Elim L a r
elimList r f = mapElimShape (view isoL)
             $ elimSum
                 (elimOne r)
                 (elimProd . elimX $ \a -> fmap (f a) (elimList r f))

instance Labelled [] where
  type ShapeOf [] = L
  toLabelled      = fromList
  fromLabelled    = elim (elimList [] (:))
