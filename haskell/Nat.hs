{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeOperators        #-}

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

class Natural (n :: Nat) where
  toSNat :: SNat n

instance Natural Z where
  toSNat = SZ

instance Natural n => Natural (S n) where
  toSNat = SS toSNat

type family Plus (m :: Nat) (n :: Nat) :: Nat
type instance Plus Z n     = n
type instance Plus (S m) n = S (Plus m n)

plus :: SNat m -> SNat n -> SNat (Plus m n)
plus SZ n     = n
plus (SS m) n = SS (plus m n)

type family Times (m :: Nat) (n :: Nat) :: Nat
type instance Times Z n     = Z
type instance Times (S m) n = Plus n (Times m n)

times :: SNat m -> SNat n -> SNat (Times m n)
times SZ _     = SZ
times (SS m) n = plus n (times m n)

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

--------------------------------------------------
-- Enumerating all the elements of Fin n

fins :: SNat n -> [Fin n]
fins SZ     = []
fins (SS n) = FZ : map FS (fins n)
