{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

------------------------------------------
-- The point of this module is to show that Traversable is the same as
-- Functor f => f # List.

module Traversal where

import BFunctor
import SpeciesTypes
import Data.Traversable
import qualified Data.Foldable as F
import qualified Vec as V
import Nat
import Proxy
import Finite

-- reify Functor dictionary
data FuncDict f = FuncDict { _tmap :: forall a b . (a -> b) -> f a -> f b }

-- reify Applicative dictionary
data ApplDict f = ApplDict {
  _func :: FuncDict f, -- is a functor
  _pure :: forall a . a -> f a,
  _app  :: forall a b . f (a -> b) -> f a -> f b }
  
-- reify Foldable dictionary
data FoldDict f = FoldDict {
  _foldr :: forall a b . (a -> b -> b) -> b -> f a -> b
}

-- we need to reify a Traversable's dictionary
data TravDict t = TravDict {
  _tfunc :: FuncDict t,
  _tfold :: FoldDict t,
  _traverse :: forall a b f . ApplDict f -> (a -> f b) -> t a -> f (t b)
}

toTrav :: Sp' (f # L) a -> TravDict (Sp' f)
toTrav (SpEx (Struct (Shape (CProd f1 f2)) elts)) = TravDict {
  _tfunc = FuncDict {_tmap = fmap},
  _tfold = FoldDict {_foldr = spfoldr},
  _traverse = undefined
}
    where
      -- need elimList to define this
      spfoldr g a (SpEx (Struct (Shape s1) els)) = undefined

fromTrav :: (F.Foldable f) => f a -> Sp (f # L) l a
fromTrav f = Struct (Shape (CProd undefined undefined)) undefined
  where x = reverse (F.toList f)
        -- very dynamic ?!?
        vIndex :: [a] -> Fin n -> a
        vIndex [x] FZ = x
        vIndex (x:xs) (FS f) = vIndex xs f
        y :: Finite l => V.Vec (Size l) a
        y = V.mkV (size (undefined :: Proxy l)) (vIndex x)
