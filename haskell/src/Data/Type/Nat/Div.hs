{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeOperators #-}
module Data.Type.Nat.Div where

import           Data.Type.Equality
import           Data.Type.Nat
import           Data.Type.Nat.Inequality
import           Data.Type.Nat.Minus

--------------------------------------------------
-- Division algorithm

data Div x n where
  Div :: SNat i -> SNat j -> (j < n) -> (x :~: Plus j (Times i n)) -> Div x n

divisionAlg :: SNat x -> SNat n -> Div x n
divisionAlg x n = case decLT n x of
  Left lt -> case plusZeroR x of Refl -> Div SZ x lt Refl
  Right (Minus x' Refl) ->
    case divisionAlg x' n of
      Div i' j lt Refl ->
        case (plusAssoc j (times i' n) n, plusComm (times i' n) n) of
          (Refl, Refl) ->
            Div (SS i') j lt Refl

