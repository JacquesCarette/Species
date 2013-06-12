{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Finite where

import           Control.Lens
import qualified Data.Void     as DV
import           Equality
import           Nat
import           Proxy

import           Unsafe.Coerce (unsafeCoerce)

------------------------------------------------------------
--  Isomorphisms

type (<->) a b = Iso' a b

type (<-->) f g = forall l. (Eq l, Finite l) => f l <-> g l

-- Lift an iso on a field to an iso of the whole structure.
liftIso :: Setter s t a b -> Setter t s b a -> (a <-> b) -> (s <-> t)
liftIso l1 l2 ab = withIso ab $ \f g -> iso (l1 %~ f) (l2 %~ g)

------------------------------------------------------------
--  Natural transformations

type (-->) f g = forall l. (Eq l, Finite l) => f l -> g l

------------------------------------------------------------
--  Constructively finite types

class Eq l => Finite l where
  type Size l :: Nat
  size        :: Proxy l -> SNat (Size l)
  finite      :: Fin (Size l) <-> l

instance Natural n => Finite (Fin n) where
  type Size (Fin n) = n
  size _ = toSNat
  finite = id

instance Finite DV.Void where
  type Size DV.Void = Z
  size _ = SZ
  finite = iso absurd DV.absurd

instance Finite () where
  type Size () = S Z
  size _ = SS SZ
  finite = iso (const ()) (const FZ)

instance Finite a => Finite (Maybe a) where
  type Size (Maybe a) = S (Size a)
  size _ = SS (size (Proxy :: Proxy a))
  finite = iso toM fromM
    where
      toM :: Fin (S (Size a)) -> Maybe a
      toM FZ         = Nothing
      toM (FS n)     = Just $ view finite n

      fromM :: Maybe a -> Fin (S (Size a))
      fromM Nothing  = FZ
      fromM (Just l) = FS (view (from finite) l)

instance Finite Bool where
  type Size (Bool) = S (S Z)
  size _ = SS (SS SZ)
  finite = iso (\s -> case s of FZ -> False; FS FZ -> True)
               (\b -> case b of False -> FZ; True -> FS FZ)

instance (Finite a, Finite b) => Finite (Either a b) where
  type Size (Either a b) = Plus (Size a) (Size b)
  size _ = plus (size (Proxy :: Proxy a)) (size (Proxy :: Proxy b))
  finite = error "finite for Either" -- XXX todo

instance (Finite a, Finite b) => Finite (a,b) where
  type Size (a,b) = Times (Size a) (Size b)
  size _ = times (size (Proxy :: Proxy a)) (size (Proxy :: Proxy b))
--  finite :: Fin (Times (Size a) (Size b)) <-> (a,b)
  finite = iso (error "finite for pairs")  -- XXX todo.  Have to do divmod.
               (\(a,b) -> finPair szA szB (getFin a) (getFin b))
    where
      szA = size (Proxy :: Proxy a)
      szB = size (Proxy :: Proxy b)
      getFin :: Finite x => x -> Fin (Size x)
      getFin = view (from finite)

  -- error "finite for pairs" -- XXX todo

------------------------------------------------------------
-- Miscellaneous proofs about size

isoPresSize :: forall l1 l2. (Finite l1, Finite l2) =>
               (l1 <-> l2) -> (Size l1 == Size l2)
isoPresSize _
  | snatEq s1 s2 = unsafeCoerce Refl
  | otherwise = error $ "isoPresSize: " ++ show s1 ++ " /= " ++ show s2
  where s1 = size (Proxy :: Proxy l1)
        s2 = size (Proxy :: Proxy l2)

  -- Can we actually implement this in Haskell?  I don't think so.
