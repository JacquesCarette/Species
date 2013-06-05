{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}

module Proxy where

import Nat

data Proxy a = Proxy

-- A variant of Proxy for type-level lists which gives us enough
-- value-level structure to pattern match on.  Similar to HVec except
-- we don't actually store any values of the given types.
data LProxy :: Nat -> [*] -> * where
  LNil  :: LProxy Z '[]
  LCons :: Proxy l -> LProxy n ls -> LProxy (S n) (l ': ls)
