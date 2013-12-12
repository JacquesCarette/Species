module Data.Species.Zippy where

import           Data.Species.Shape
import           Data.Species.Types
import           Data.Finite        (Size(..),Finite(..))
import qualified Data.Storage as S
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

zipS :: (Zippy f, S.Storage s) => Sp f s l a -> Sp f s l b -> Sp f s l (a,b)
zipS = zipWithS (,)

zipWithS :: (Zippy f, S.Storage s) => (a -> b -> c) -> Sp f s l a -> Sp f s l b -> Sp f s l c
zipWithS f (Struct shA as) (Struct shB bs) = 
    Struct (fzip shA shB) (S.zipWith f as bs)
