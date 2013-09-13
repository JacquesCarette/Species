module Data.Species.Cursor where

import           Data.BFunctor
import           Data.Species.Shape
import           Data.Species.Types

-- XXX hmm, this is not the right type.  FComp f (P f) is an f-shape
-- containing ALL POSSIBLE (P f)-shapes, but we only want the ones
-- that match the shape of f.
down :: BFunctor f => Sp f l a -> Sp (FComp f (P f)) l a
down (Struct fl as)
  = Struct (fcomp_ undefined undefined) as
