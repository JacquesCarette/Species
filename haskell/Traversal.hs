{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

------------------------------------------
-- The point of this module is to show that Traversable is the same as
-- Functor f => f # List.

module Traversal where

import SpeciesTypes
import qualified Data.Traversable as T
import qualified Data.Foldable as F
import Control.Applicative
import qualified Nat as N
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

-- can get a L-structure from just Foldable
fromFold :: F.Foldable f => f a -> Sp' L a
fromFold f = fromList $ F.foldr (:) [] f

-- useful utility routine for below
replace :: a -> WriterT [a] (Supply l) l
replace a = do
  l <- supply
  tell [a]
  return l

-- so of course, it can be done from Traversable too:
toL :: T.Traversable f => f a -> Sp' L a
toL = fromList . execWriter . T.traverse rep'
  where
    rep' :: a -> Writer [a] ()
    rep' a = do tell [a]; return () 

fromTrav :: T.Traversable f => f a -> Sp' (f # L) a
fromTrav fa = let ll = F.foldr (:) [] fa in
              case fromList ll of
                SpEx sp@(Struct (Shape l) v) -> 
                  SpEx (Struct (Shape (CProd fl l)) v)
                  where fl = fst . evalSup m $ toList sp
                        m = runWriterT . T.traverse replace $ fa

toList :: Eq l => Sp L l a -> [l]
toList (Struct shp _) = case elimList [] (:) of Elim f -> f shp id

evalSup :: Supply s (f s, [a]) -> [s] -> (f s, [a])
evalSup m l = flip evalSupply l m

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

{-
instance T.Traversable (Sp' (g # L)) where
  -- traverse :: Applicative f => (a -> f b) -> t a -> f (t b)
  --  where t = Sp' (g # L)
  traverse f l = case l of
                   SpEx (Struct (Shape (CProd f1 l1)) v) ->
                     let sp = Struct (Shape l1) v in
                     let lt = T.traverse f (toList sp) in
-}
