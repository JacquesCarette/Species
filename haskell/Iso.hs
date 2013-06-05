{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeOperators #-}

module Iso where

import Control.Lens

type (<->) a b = Iso' a b

type (<-->) f g = forall l. f l <-> g l

-- Lift an iso on a field to an iso of the whole structure.
liftIso :: Setter s t a b -> Setter t s b a -> (a <-> b) -> (s <-> t)
liftIso l1 l2 ab = withIso ab $ \f g -> iso (l1 %~ f) (l2 %~ g)
