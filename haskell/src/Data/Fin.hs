{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators      #-}

module Data.Fin where

import Data.Type.Nat.Inequality
import Data.Type.Nat
import Unsafe.Coerce
  -- for eliminating Fin Z

------------------------------------------------------------
-- Finite types

data Fin :: Nat -> * where
  FZ :: Fin (S n)
  FS :: Fin n -> Fin (S n)

deriving instance Show (Fin n)
deriving instance Eq (Fin n)

fin :: r -> (r -> r) -> Fin n -> r
fin z _ FZ     = z
fin z s (FS n) = s (fin z s n)

finToInt :: Fin n -> Int
finToInt = fin 0 succ

absurd :: Fin Z -> a
absurd = unsafeCoerce

--------------------------------------------------
-- Enumerating all the elements of Fin n

fins :: SNat n -> [Fin n]
fins SZ     = []
fins (SS n) = FZ : map FS (fins n)

--------------------------------------------------
-- FinN

-- FinN n is isomorphic to Fin n, but much easier to work with
-- directly, since it lets us do arithmetic and construct the
-- necessary proofs separately.

data FinN :: Nat -> * where
  FinN :: SNat i -> (i < n) -> FinN n

-- Conversion functions witnessing the isomorphism.

finToFinN :: Fin n -> FinN n
finToFinN FZ     = FinN SZ (LTES LTEZ)
finToFinN (FS i) =
  case finToFinN i of
    (FinN j jLTn) -> FinN (SS j) (LTES jLTn)

finNToFin :: FinN n -> Fin n
finNToFin (FinN SZ (LTES _))        = FZ
finNToFin (FinN (SS i) (LTES iLTn)) = FS (finNToFin (FinN i iLTn))
