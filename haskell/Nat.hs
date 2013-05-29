{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE Rank2Types         #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators      #-}

module Nat where

import BFunctor
import Control.Lens
import Data.Void

------------------------------------------------------------
-- Natural numbers

data Nat = Z | S Nat
  deriving (Eq, Ord, Show)

nat :: r -> (r -> r) -> Nat -> r
nat z s Z     = z
nat z s (S n) = s (nat z s n)

natToInt :: Nat -> Int
natToInt = nat 0 succ

intToNat :: Int -> Nat
intToNat 0 = Z
intToNat n = S (intToNat (n-1))

------------------------------------------------------------
-- Singleton Nats

data SNat :: Nat -> * where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

deriving instance Show (SNat n)

snat :: r -> (r -> r) -> SNat n -> r
snat z s SZ     = z
snat z s (SS n) = s (snat z s n)

snatToInt :: SNat n -> Int
snatToInt = snat 0 succ

type family Plus (m :: Nat) (n :: Nat) :: Nat
type instance Plus Z n     = n
type instance Plus (S m) n = S (Plus m n)

plus :: SNat m -> SNat n -> SNat (Plus m n)
plus SZ n     = n
plus (SS m) n = SS (plus m n)

------------------------------------------------------------
-- Finite types

data Fin :: Nat -> * where
  FZ :: Fin (S n)
  FS :: Fin n -> Fin (S n)

deriving instance Show (Fin n)
deriving instance Eq (Fin n)

fin :: r -> (r -> r) -> Fin n -> r
fin z s FZ     = z
fin z s (FS n) = s (fin z s n)

finToInt :: Fin n -> Int
finToInt = fin 0 succ

------------------------------------------------------------
-- Proofs of finiteness

plusPf :: (Fin m <-> l1) -> (Fin n <-> l2) -> Fin (Plus m n) <-> (Either l1 l2)
plusPf = undefined  -- XXX TODO


data Finite :: * -> * where
  Finite :: (l <-> Fin n) -> Finite l

class IsFinite l where
  finite :: Finite l

instance IsFinite Void where
  finite = Finite (undefined :: Void <-> Fin Z)

instance IsFinite () where
  finite = Finite (iso (const FZ) (const ()) :: () <-> Fin (S Z))

instance IsFinite Bool where
  finite = Finite (iso (\b -> case b of False -> FZ; True -> FS FZ)
                       (\s -> case s of FZ -> False; FS FZ -> True)
                       :: Bool <-> Fin (S (S Z))
                  )

instance (IsFinite a, IsFinite b) => IsFinite (Either a b) where
  finite = undefined -- XXX todo

instance (IsFinite a, IsFinite b) => IsFinite (a,b) where
  finite = undefined -- XXX todo
