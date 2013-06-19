{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}

------------------------------------------
-- The point of this module is to show that Traversable is the same as
-- Functor f => f # List.

module Traversal where

import SpeciesTypes
import Data.Traversable
import qualified Data.Foldable as F
import Control.Applicative
import Finite
import qualified Vec as V
import qualified Prelude as P

{- we would like:
fromTrav :: (F.Foldable f) => f a -> Sp' (f # L) a
but we can at least get:
-}
fromFold :: F.Foldable f => f a -> Sp' L a
fromFold f = fromList l
  where l = F.foldr (:) [] f

-- All of these are valid:
instance Finite l => F.Foldable (Sp L l) where
  foldr f b (Struct (Shape f2) elts) =
    elim (elimList b f) (Struct (Shape f2) elts)

instance Finite l => F.Foldable (Sp (f # L) l) where
  foldr f b (Struct (Shape (CProd _ f2)) elts) =
    elim (elimList b f) (Struct (Shape f2) elts)

instance F.Foldable (Sp' (f # L)) where
  foldr f b (SpEx (Struct (Shape (CProd _ f2)) elts)) =
    elim (elimList b f) (Struct (Shape f2) elts)
