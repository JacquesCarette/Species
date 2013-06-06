{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE Rank2Types #-}

module SpeciesIsos where

import Iso
import Nat
import Control.Lens
import SpeciesTypes

plusC :: (f + g) <--> (g + f)
plusC = iso swap swap
        where
          swap (Inl x) = Inr x
          swap (Inr x) = Inl x

isoPlus :: Sp (f + g) l a <-> Sp (g + f) l a
isoPlus = reshape' plusC
