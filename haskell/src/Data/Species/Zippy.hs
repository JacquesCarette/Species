module Data.Species.Zippy where

import           Data.Species.Shape
import           Data.Species.Types
import qualified Data.Vec           as V
import           Data.Finite
import           Control.Lens

-- For labelled species, only things whose shape has no real content
-- are zippy, since we need to be able to match up the shapes AND the
-- labels.

class Zippy f where
  fzip :: f l -> f l -> f l

instance Zippy One where
  fzip o _ = o

instance Zippy X where
  fzip x _ = x

instance Zippy E where
  fzip x _ = x

zipS :: (Zippy f, HasSize l) => Sp f l a -> Sp f l b -> Sp f l (a,b)
zipS = zipWithS (,)

zipWithS :: (Zippy f, HasSize l) => (a -> b -> c) -> Sp f l a -> Sp f l b -> Sp f l c
zipWithS f (Struct shA as finA@(F isoA)) (Struct shB bs finB@(F isoB)) = 
    Struct (fzip shA shB) (V.zipWith f as bs') finA
    where bs' = V.permute (size finA) (isoA . from isoB) bs
