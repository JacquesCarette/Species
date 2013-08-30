{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE Rank2Types    #-}
{-# LANGUAGE TypeOperators #-}

-- | Some isomorphisms of species.  Note that only isomorphisms of
--   labelled shapes are provided; lifting these to isomorphisms of
--   labelled structures can be accomplished with 'relabel' and
--   'relabel''.
module Data.Species.Isos
    ( zeroCancel, oneCancel
    , sumComm, prodComm

    ) where

import           Control.Lens

import           Data.BFunctor
import           Data.Finite
import           Data.Species.Shape
import           Data.Type.Isos

-- XXX need to add a bunch more!

zeroCancel :: (Zero * f) <--> Zero
zeroCancel = iso elimZf absurdZ
             where
               elimZf :: (Zero * f) l -> a
               elimZf (Prod x _ _) = absurdZ x

oneCancel :: BFunctor f => (One * f) <--> f
oneCancel = iso
  (\(Prod (One x) y i) -> view (bmap (from zeroPL . liftIso _Left _Left x . i)) y)
                           {- l2 ~ Either Void l2 ~  Either l1 l2 ~ l -}
  (\fl -> Prod (One id) fl zeroPL)

sumComm :: (f + g) <--> (g + f)
sumComm = iso swap swap
           where
             swap (Inl x) = Inr x
             swap (Inr x) = Inl x

prodComm :: (f * g) <--> (g * f)
prodComm = iso swap swap
             where
               swap (Prod x y i) = Prod y x (commP . i)
