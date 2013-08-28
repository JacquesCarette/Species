{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeOperators #-}

module Data.Type.Nat.Minus where

import           Data.Type.Equality
import           Data.Type.Nat
import           Data.Type.Nat.Inequality

--------------------------------------------------
-- Type-level subtraction and decidable ordering

data Minus x n where
  Minus :: SNat j -> (x :=: Plus j n) -> Minus x n

decLT :: SNat n -> SNat x -> Either (x < n) (x `Minus` n)
decLT SZ x = case plusZeroR x of Refl -> Right (Minus x Refl)
decLT (SS _) SZ = Left (LTES LTEZ)
decLT (SS n) (SS x) = case decLT n x of
  Left xLTn            -> Left (LTES xLTn)
  Right (Minus j Refl) -> case plusSuccR j n of Refl -> Right (Minus j Refl)

-- computes x - n knowing that n <= x
minus :: SNat x -> SNat n -> (n <= x) -> (x `Minus` n)
minus x SZ _ = case plusZeroR x of Refl -> Minus x Refl
minus (SS x) (SS n) (LTES n_le_x) =
    case minus x n n_le_x of
      Minus y Refl ->
        case plusSuccR y n of Refl -> Minus y Refl


