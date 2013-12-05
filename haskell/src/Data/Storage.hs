{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Data.Storage
    ( Storage(..)
    , emptyStorage
    )
    where

import Prelude hiding (zip, zipWith, concat)

import Data.Type.Nat
import Data.Fin
import Data.Finite
import Data.Subset

-- This shouldn't really need to have l as a parameter, but otherwise
-- we can't express the Functor constraint =(

class Storage s where
  allocate :: Finite l -> (l -> a) -> s l a
  reindex  :: (l' ⊆ l) -> s l a -> s l' a

  index  :: s l a -> l -> a
  lookup :: Eq a => s l a -> a -> Maybe l

  replace :: l -> a -> s l a -> (a, s l a)

  append :: s l1 a -> s l2 a -> s (Either l1 l2) a
  concat :: s l1 (s l2 a) -> s (l1,l2) a

  zipWith :: (a -> b -> c) -> s l a -> s l b -> s l c

emptyStorage :: Storage s => s (Fin Z) a
emptyStorage = allocate finite_Fin absurd
