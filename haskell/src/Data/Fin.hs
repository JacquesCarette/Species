{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators      #-}

module Data.Fin
    ( -- * Size-indexed finite sets

      Fin(..), absurd, fin, finToInt, fins

      -- * Separating arithmetic and proofs on @Fin@

    , FinN(..), finToFinN, finNToFin
    )
    where

import Data.Type.Nat.Inequality
import Data.Type.Nat
import Unsafe.Coerce
  -- for eliminating Fin Z

------------------------------------------------------------
-- Finite types

-- | @Fin n@ is the canonical type with exactly @n@ (non-partial)
--   inhabitants.
data Fin :: Nat -> * where
  FZ :: Fin (S n)
  FS :: Fin n -> Fin (S n)

deriving instance Show (Fin n)
deriving instance Eq (Fin n)

-- | Generic eliminator for @Fin@ values.
fin :: r -> (r -> r) -> Fin n -> r
fin z _ FZ     = z
fin z s (FS n) = s (fin z s n)

-- | Convert a @Fin n@ value to an 'Int' in the range 0 to (n-1).
finToInt :: Fin n -> Int
finToInt = fin 0 succ

-- | @Fin Z@ is uninhabited.
absurd :: Fin Z -> a
absurd = unsafeCoerce

--------------------------------------------------
-- Enumerating all the elements of Fin n

-- | A list of all the values of type @Fin n@, in order from smallest
--   (@FZ@) to largest.
fins :: SNat n -> [Fin n]
fins SZ     = []
fins (SS n) = FZ : map FS (fins n)

--------------------------------------------------
-- FinN

-- | @FinN n@ is isomorphic to @Fin n@ (as witnessed by the inverse
--   pair of 'finToFinN' and 'finNToFin'), but is sometimes much
--   easier to work with directly, since it lets us do arithmetic (on
--   @SNat@ values) and construct the necessary proofs (see
--   "Data.Type.Nat.Inequality") separately.
data FinN :: Nat -> * where
  FinN :: SNat i -> (i < n) -> FinN n

-- | One half of an isomorphism between @Fin n@ and @FinN n@.
finToFinN :: Fin n -> FinN n
finToFinN FZ     = FinN SZ (LTES LTEZ)
finToFinN (FS i) =
  case finToFinN i of
    (FinN j jLTn) -> FinN (SS j) (LTES jLTn)

-- | The other half of the isomorphism.
finNToFin :: FinN n -> Fin n
finNToFin (FinN SZ (LTES _))        = FZ
finNToFin (FinN (SS i) (LTES iLTn)) = FS (finNToFin (FinN i iLTn))

{- finNToFin (finToFinN FZ) = FinNToFin (FinN SZ (LTES LTEZ)) = FZ

   finNToFin (finToFinN (FS f))
   = finNToFin (case finToFinN f of (FinN j jLTn) -> FinN (SS j) (LTES jLTn))
   = case finToFinN f of (FinN j jLTn) -> finNToFin (FinN (SS j) (LTES jLTn))
   = case finToFinN f of (FinN j jLTn) -> FS (finNToFin (FinN j jLTn))
   = FS (finNToFin (case finToFinN f of (FinN j jLTn) -> FinN j jLTn))
   = FS (finNToFin (finToFinN f))
   = FS f

-}
