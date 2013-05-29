{-# LANGUAGE Rank2Types     #-}
{-# LANGUAGE TypeOperators  #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds      #-}

module Fin where

import BFunctor
import Control.Lens
import Data.Void

data Nat = Z | S Nat

data Fin :: Nat -> * where
  FZ :: Fin (S n)
  FS :: Fin n -> Fin (S n)

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
