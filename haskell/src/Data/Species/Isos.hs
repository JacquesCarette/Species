{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE Rank2Types    #-}
{-# LANGUAGE TypeOperators #-}

module Data.Species.Isos where

import           Control.Lens

import           Data.BFunctor
import           Data.Finite
import           Data.Species.Types
import           Data.Type.Isos

import           Unsafe.Coerce

absurdS :: Zero l -> a
absurdS = unsafeCoerce

zeroCancel :: (Zero * f) <--> Zero
zeroCancel = iso elimZf absurdS
             where
               elimZf :: (Zero * f) l -> a
               elimZf (Prod x y i) = absurdS x

oneCancel :: BFunctor f => (One * f) <--> f
oneCancel = iso
  (\(Prod (One x) y i) -> view (bmap (from zeroPL . liftIso _Left _Left x . i)) y)
                           {- l2 ~ Either Void l2 ~  Either l1 l2 ~ l -}
  (\fl -> Prod (One id) fl zeroPL)

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

isoPlus :: Finite l => Sp (f + g) l a <-> Sp (g + f) l a
isoPlus = reshape' plusComm

isoTimes :: Finite l => Sp (f * g) l a <-> Sp (g * f) l a
isoTimes = reshape' timesComm
