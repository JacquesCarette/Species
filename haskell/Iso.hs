{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeOperators #-}

module Iso where

import Control.Lens

type (<->) a b = Iso' a b

type (<-->) f g = forall l. f l <-> g l

