{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}
module Data.Species.List where

import           Control.Lens       (Iso, from, iso, view)

import           Data.BFunctor
import           Data.Fin
import           Data.Finite
import           Data.Species.Elim
import           Data.Species.Shape
import           Data.Species.Types
import           Data.Type.Nat
import qualified Data.Vec           as V


-- List ------------------------------------------

-- It turns out we don't need all that complicated type-level
-- machinery to do recursive labelled structures.  We can just embed
-- the recursion within Haskell by defining recursive shapes directly.
-- Here's an example.

newtype L l = L { unL :: (One + X * L) l }

isoL :: Iso (L l) (L l') ((One + X*L) l) ((One + X*L) l')
isoL = iso unL L

instance BFunctor L where
  bmap g = liftIso isoL isoL (bmap g)

-- Some introduction forms for lists, and an example of converting a
-- Haskell list to a Sp' L.  Ideally all of this would be generically
-- derivable.

list_ :: Finite l => (One + X*L) l -> L l
list_ = view (from isoL)

list :: Finite l => Sp (One + X*L) l a -> Sp L l a
list = reshape (view (from isoL))

nil :: Sp L (Fin Z) a
nil = list $ inl one

cons :: (Eq l', Finite l') => a -> Sp L l' a -> Sp L (Either (Fin (S Z)) l') a
cons a (Struct shp es) = Struct (list_ (inr_ (prod_ x_ shp))) (V.VCons a es)

fromList :: [a] -> Sp' L a
fromList [] = SpEx nil
fromList (a:as) =
  case fromList as of
    SpEx s -> SpEx (cons a s)

elimList :: r -> (a -> r -> r) -> Elim L a r
elimList r f = mapElimShape (view isoL)
             $ elimSum
                 (elimOne r)
                 (elimProd . elimX $ \a -> fmap (f a) (elimList r f))

