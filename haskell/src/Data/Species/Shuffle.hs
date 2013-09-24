{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ImpredicativeTypes  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
module Data.Species.Shuffle where

import           Control.Lens
import           Control.Monad.Writer
-- from 'representable-functors' package
import           Data.Functor.Representable
-- from 'keys' package
import           Data.Key                   (Key, TraversableWithKey)
import qualified Data.Key                   as K
import           Data.Maybe                 (fromJust)
import           Data.Tuple                 (swap)

import           Data.BFunctor
import           Data.Finite
import           Data.Species.Shape
import           Data.Species.Types


canonicalize :: forall f l a. (TraversableWithKey f, Size (Key f) ~ Size l, Eq l, Eq (Key f), HasSize (Key f))
             => Sp f l a -> (Sp f (Key f) a, l <-> Key f)
canonicalize (Struct fl es fin) = (Struct fk es (finConv klIso fin), klIso)
  where
    (fk, m) = runWriter (K.mapWithKeyM (\k l -> tell [(k,l)] >> return k) fl)
    klIso :: l <-> Key f
    klIso   = iso (fromJust . (lookup ?? map swap m)) (fromJust . (lookup ?? m))

forgetShape :: Sp f l a -> Sp E l a
forgetShape (Struct _ es finl) = Struct (e_ finl) es finl

reconstitute :: Representable f => Sp E (Key f) a -> Sp f (Key f) a
reconstitute (Struct _ es finl) = Struct (tabulate id) es finl

unCanonicalize :: (BFunctor f, Representable f, HasSize l, HasSize (Key f), Eq l, Eq (Key f))
               => (Sp f (Key f) a, l <-> Key f) -> Sp f l a
unCanonicalize (sp, i) = relabel (from i) (reconstitute . forgetShape $ sp)
