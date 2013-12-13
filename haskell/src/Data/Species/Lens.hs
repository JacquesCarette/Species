{- Lenses into Species -}
{-# LANGUAGE RankNTypes, ConstraintKinds #-}
module Data.Species.Lens where

import           Control.Lens

import           Data.Finite
import           Data.Species.Shape (P(..))
import           Data.Species.Types (Sp(..))
import qualified Data.Storage as S

lensSp :: (S.Storage s, S.LabelConstraint s l) => l -> Lens' (Sp f s l a) a
lensSp lbl = 
    lens (\(Struct _ e) -> S.index e lbl)
         (\(Struct sh e) a -> Struct sh (snd $ S.replace lbl a e))
