{-# LANGUAGE DataKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeOperators #-}

module SpeciesIsos where

import Iso
import Nat
import Control.Lens
import BFunctor
import SpeciesTypes

import Unsafe.Coerce -- for eliminating Zero

absurdS :: Zero l -> a
absurdS = unsafeCoerce

zeroCancel :: (Zero * f) <--> Zero
zeroCancel = iso (absurdS . elimZ) absurdS
             where
               elimZ :: (Zero * f) l -> Zero l
               elimZ (Prod x y i) = undefined -- FIXME

oneCancel :: (One * f) <--> f
oneCancel = iso (\(Prod (One x) y i) -> undefined) undefined  -- FIXME

plusComm :: (f + g) <--> (g + f)
plusComm = iso swap swap
           where
             swap (Inl x) = Inr x
             swap (Inr x) = Inl x

timesComm :: (f * g) <--> (g * f)
timesComm = iso swap swap
             where
               swap (Prod x y i) = Prod y x (commP . i)

------------------------------
-- Some species isomorphisms

isoPlus :: Sp (f + g) l a <-> Sp (g + f) l a
isoPlus = reshape' plusComm

isoTimes :: Sp (f * g) l a <-> Sp (g * f) l a 
isoTimes = reshape' timesComm
