{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeOperators        #-}

module Nat where

import Control.Lens
import Iso

import Unsafe.Coerce  -- for eliminating Fin Z

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

snatEq :: SNat m -> SNat n -> Bool
snatEq SZ SZ         = True
snatEq (SS m) (SS n) = snatEq m n
snatEq _ _           = False

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

absurd :: Fin Z -> a
absurd = unsafeCoerce

--------------------------------------------------
-- Enumerating all the elements of Fin n

fins :: SNat n -> [Fin n]
fins SZ     = []
fins (SS n) = FZ : map FS (fins n)

------------------------------------------------------------
-- Some arithmetic isomorphisms

zeroL :: (Fin Z, a) <-> Fin Z
zeroL = iso (absurd . fst) absurd

oneL :: ((), a) <-> a
oneL = iso snd ((,) ())

distribR :: (Either a b, c) <-> Either (a,c) (b,c)
distribR = iso distribR1 distribR2
  where
    distribR1 (Left a, c)   = Left (a,c)
    distribR1 (Right b, c)  = Right (b,c)
    distribR2 (Left (a,c))  = (Left a, c)
    distribR2 (Right (b,c)) = (Right b, c)

succFin :: Either () (Fin m) <-> Fin (S m)
succFin = iso succFin1 succFin2
  where
    succFin1 (Left ()) = FZ
    succFin1 (Right f) = FS f

    succFin2 :: Fin (S m) -> Either () (Fin m)
    succFin2 FZ        = Left ()
    succFin2 (FS f)    = Right f
