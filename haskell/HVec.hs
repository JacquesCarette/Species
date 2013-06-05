{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators  #-}
{-# LANGUAGE DataKinds      #-}

module HVec where

import Nat

-- Length-indexed, type-indexed heterogeneous vectors
data HVec :: Nat -> [*] -> * where
  HNil   :: HVec Z '[]
  HCons  :: l -> HVec n ls -> HVec (S n) (l ': ls)

