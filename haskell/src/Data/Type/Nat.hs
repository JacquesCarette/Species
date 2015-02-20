{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Type.Nat where

import           Data.Type.Equality

------------------------------------------------------------
-- Natural numbers

data Nat = Z | S Nat
  deriving (Eq, Ord, Show)

------------------------------------------------------------
-- Singleton Nats

data SNat :: Nat -> * where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

deriving instance Show (SNat n)

snat :: r -> (r -> r) -> SNat n -> r
snat z _ SZ     = z
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

natty :: SNat n -> (Natural n => r) -> r
natty SZ r     = r
natty (SS n) r = natty n r

--------------------------------------------------
-- Properties of addition and multiplication

plusZeroR :: SNat n -> Plus n Z :~: n
plusZeroR SZ     = Refl
plusZeroR (SS n) = case plusZeroR n of Refl -> Refl

plusSuccR :: SNat m -> SNat n -> Plus m (S n) :~: S (Plus m n)
plusSuccR SZ _     = Refl
plusSuccR (SS m) n = case plusSuccR m n of Refl -> Refl

plusAssoc :: SNat a -> SNat b -> SNat c -> (Plus (Plus a b) c) :~: Plus a (Plus b c)
plusAssoc SZ _ _ = Refl
plusAssoc (SS a) b c = case plusAssoc a b c of Refl -> Refl

plusComm :: SNat a -> SNat b -> Plus a b :~: Plus b a
plusComm SZ b = case plusZeroR b of Refl -> Refl
plusComm (SS a) b = case (plusSuccR b a, plusComm a b) of (Refl, Refl) -> Refl

mulZeroR :: SNat x -> Times x Z :~: Z
mulZeroR SZ = Refl
mulZeroR (SS x) = mulZeroR x

