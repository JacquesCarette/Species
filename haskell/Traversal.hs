{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}

------------------------------------------
-- The point of this module is to show that Traversable is the same as
-- Functor f => f # List.

module Traversal where

import SpeciesTypes
import qualified Data.Traversable as T
import qualified Data.Foldable as F
import Control.Applicative
import Finite
import qualified Vec as V

import Control.Monad.Writer
import Control.Monad.Supply

-- Use this orphan instance until
-- https://github.com/ghulette/monad-supply/pull/3 is merged and
-- released
instance Applicative (Supply s) where
  pure  = return
  (<*>) = ap

fromFold :: F.Foldable f => f a -> Sp' L a
fromFold f = fromList l
  where l = F.foldr (:) [] f

fromTrav :: T.Traversable f => f a -> Sp' (f # L) a
fromTrav = mkSp' . T.traverse replace
  where
    replace :: a -> WriterT [a] (Supply Int) Int
    replace a = do
      l <- supply
      tell [a]
      return l
    mkSp' m =
      let (fl, as) = flip evalSupply [0..] . runWriterT $ m
      in  undefined
          -- case V.fromList as of
          --   (V.SomeVec v) ->
          --     SpEx (Struct (Shape (fmap undefined fl)) v)

        -- convert all Ints to Fin n for some n, convert as to vector,
        -- pair up with L shape

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
