{- Lenses into Species -}
{-# LANGUAGE RankNTypes #-}
module Data.Species.Lens where

import           Control.Lens

import           Data.Finite
import           Data.Species.Shape (P(..))
import           Data.Species.Types (Sp(..))
import qualified Data.Vec           as V

lensSp :: l -> Lens' (Sp f l a) a
lensSp lbl = 
    lens (\(Struct _ e finl) -> V.index e $ toFin finl lbl)
         (\(Struct sh e finl) a -> 
             Struct sh (V.replace (toFin finl lbl) a e) finl)
