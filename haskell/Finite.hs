{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Finite where

import BFunctor
import Control.Lens
import Data.Void
import Nat
import Proxy

class Finite l where
  type Size l :: Nat
  size   :: Proxy l -> Int
  finite :: Fin (Size l) <-> l

instance Natural n => Finite (Fin n) where
  type Size (Fin n) = n
  size _ = snatToInt (toSNat :: SNat n)
  finite = id

instance Finite Void where
  type Size Void = Z
  size _ = 0
  finite = undefined

instance Finite () where
  type Size () = S Z
  size _ = 1
  finite = iso (const ()) (const FZ)

instance Finite Bool where
  type Size (Bool) = S (S Z)
  size _ = 2
  finite = iso (\s -> case s of FZ -> False; FS FZ -> True)
               (\b -> case b of False -> FZ; True -> FS FZ)

instance (Finite a, Finite b) => Finite (Either a b) where
  type Size (Either a b) = Plus (Size a) (Size b)
  size _ = size (Proxy :: Proxy a) + size (Proxy :: Proxy b)
  finite = undefined -- XXX todo

instance (Finite a, Finite b) => Finite (a,b) where
  type Size (a,b) = Times (Size a) (Size b)
  size _ = size (Proxy :: Proxy a) * size (Proxy :: Proxy b)
  finite = undefined -- XXX todo
