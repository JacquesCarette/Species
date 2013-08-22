{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ImpredicativeTypes  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
module Shuffle where

import           Control.Lens
import           Control.Monad.Writer
import           Data.Key             (Key, TraversableWithKey)
import qualified Data.Key             as K
import           Data.Maybe           (fromJust)
import           Data.Tuple           (swap)

import           Finite
import           SpeciesTypes


canonicalize :: forall f l a. (TraversableWithKey f, Size (Key f) ~ Size l, Eq l, Eq (Key f))
             => Sp f l a -> (Sp f (Key f) a, l <-> Key f)
canonicalize (Struct (Shape fl) es) = (Struct (Shape fk) es, klIso)
  where
    (fk, m) = runWriter (K.mapWithKeyM (\k l -> tell [(k,l)] >> return k) fl)
    klIso :: l <-> Key f
    klIso   = iso (fromJust . (lookup ?? map swap m)) (fromJust . (lookup ?? m))
