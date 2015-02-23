{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ImpredicativeTypes  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
module Data.Species.Shuffle where

import           Control.Lens
import           Control.Monad.Writer
-- from 'adjunctions' package
import           Data.Functor.Rep
-- from 'keys' package
import           Data.Key             (Key, TraversableWithKey)
import qualified Data.Key             as K
import           Data.Maybe           (fromJust)
import           Data.Tuple           (swap)

import           Data.BFunctor
import           Data.Finite          (Size (..), finConv)
import           Data.Iso
import qualified Data.Set.Abstract    as S
import           Data.Species.Shape
import           Data.Species.Types
import           Data.Storage


canonicalize :: forall f s l a. (TraversableWithKey f, Size (Key f) ~ Size l, Eq l, Eq (Key f), HasSize (Key f), Storage s)
             => Sp f s l a -> (Sp f s (Key f) a, l <-> Key f)
canonicalize (Struct fl es) = (Struct fk (reindex klIso es), klIso)
  where
    (fk, m) = runWriter (K.mapWithKeyM (\k l -> tell [(k,l)] >> return k) fl)
    klIso :: l <-> Key f
    klIso   = iso (fromJust . (lookup ?? map swap m)) (fromJust . (lookup ?? m))

forgetShape :: S.Enumerable l => Sp f s l a -> Sp E s l a
forgetShape (Struct _ es) = Struct (e_ S.enumS) es

reconstitute :: (Representable f, Key f ~ Rep f) => Sp E s (Key f) a -> Sp f s (Key f) a
reconstitute (Struct _ es) = Struct (tabulate id) es

unCanonicalize :: (BFunctor f, Representable f, HasSize l, HasSize (Key f), Eq l, Eq (Key f), Storage s, S.Enumerable (Key f), Key f ~ Rep f)
               => (Sp f s (Key f) a, l <-> Key f) -> Sp f s l a
unCanonicalize (sp, i) = relabel (from i) (reconstitute . forgetShape $ sp)
