{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

------------------------------------------
-- The point of this module is to show that Traversable is the same as
-- Functor f => f # List.

module Data.Species.Traversal where

import           Control.Monad.Supply
import           Control.Monad.Writer
import qualified Data.Foldable        as F
import qualified Data.Traversable     as T

import           Data.Finite

import           Data.Species.Types

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
fromTrav fa = case fromFold fa of
                SpEx sp@(Struct l v) ->
                  SpEx (Struct (CProd fl l) v)
                  where fl = fst . evalSupply m $ toList sp
                        m = runWriterT . T.traverse replace $ fa

toList :: Eq l => Sp L l a -> [l]
toList (Struct shp _) = case elimList [] (:) of Elim f -> f shp id

-- All of these are valid:
instance Finite l => F.Foldable (Sp L l) where
  foldr f b (Struct f2 elts) =
    elim (elimList b f) (Struct f2 elts)

instance Finite l => F.Foldable (Sp (f # L) l) where
  foldr f b (Struct (CProd _ f2) elts) =
    elim (elimList b f) (Struct f2 elts)

instance F.Foldable (Sp' (f # L)) where
  foldr f b (SpEx (Struct (CProd _ f2) elts)) =
    elim (elimList b f) (Struct f2 elts)

{-

Basic idea: get the 'L l' structure, traverse that, and use
the resulting f [l] to decode what should be there.

And fundamentally this is false, as there is no 'left to right'
in g, not matter what the super-imposed L-structure says.

instance T.Traversable (Sp' (g # L)) where
  -- traverse :: Applicative f => (a -> f b) -> t a -> f (t b)
  --  where t = Sp' (g # L)
  traverse f l = case l of
                   SpEx (Struct (CProd f1 l1) v) ->
                     let sp = Struct l1 v in
                     let lt = T.traverse f (toList sp) in
-}
