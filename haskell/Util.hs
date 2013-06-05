{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Util where

-- Some utilities for working with type-level lists

import Nat

type family Map (f :: k1 -> k2) (as :: [k1]) :: [k2]
type instance Map f '[] = '[]
type instance Map f (a ': as) = f a ': Map f as

type family Sum (ls :: [*]) :: *
type instance Sum '[]       = Fin Z
type instance Sum (l ': ls) = Either l (Sum ls)

