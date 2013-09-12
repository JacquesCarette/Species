{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE PolyKinds       #-}
{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE TypeFamilies    #-}
{-# LANGUAGE TypeOperators   #-}

module Data.Type.List where

-- Some utilities for working with type-level lists

import GHC.Exts (Constraint)

import Control.Lens
import Data.Fin
import Data.Finite
import Data.Proxy
import Data.Type.Equality
import Data.Type.Isos
import Data.Type.Nat

type family Map (f :: k1 -> k2) (as :: [k1]) :: [k2]
type instance Map f '[]       = '[]
type instance Map f (a ': as) = f a ': Map f as

type family Sum (ls :: [*]) :: *
type instance Sum '[]       = Fin Z
type instance Sum (l ': ls) = Either l (Sum ls)

type family Replicate (n :: Nat) (a :: k) :: [k]
type instance Replicate Z     a = '[]
type instance Replicate (S n) a = a ': Replicate n a

type family (!!) (as :: [*]) (n :: Nat) :: *
type instance (a ': as) !! Z     = a
type instance (a ': as) !! (S n) = as !! n

type family All (p :: k -> Constraint) (ts :: [k]) :: Constraint
type instance All p '[] = ()
type instance All p (t ': ts) = (p t, All p ts)

lpRep :: SNat n -> Proxy l -> LProxy n (Replicate n l)
lpRep SZ _ = LNil
lpRep (SS n) p = LCons p (lpRep n p)

mapRep :: SNat n -> Proxy g -> Proxy l -> Map g (Replicate n l) :=: Replicate n (g l)
mapRep SZ     _ _ = Refl
mapRep (SS n) pg pl = case mapRep n pg pl of Refl -> Refl

allRep :: p l => SNat n -> Proxy p -> Proxy l -> (All p (Replicate n l) => r) -> r
allRep SZ     _ _ r = r
allRep (SS n) p l r = allRep n p l r

sumRepIso :: forall l1 l2. Finite l1
          => Proxy l1 -> Sum (Replicate (Size l1) l2) <-> (l1, l2)
sumRepIso p = sumRepIso' (size p) . liftIso _1 _1 finite

-- For finite m, a + ... + a (m times) = m*a
sumRepIso' :: SNat m -> (Sum (Replicate m a) <-> (Fin m, a))
sumRepIso' SZ = from zeroTL
  {-
       Sum (Replicate Z a)
   ~           { def. of Replicate }
       Sum '[]
   ~           { def. of Sum }
       Fin Z
   <->         { from zeroTL }
       (Fin Z, a)
  -}

sumRepIso' (SS m) = liftIso _Right _Right (sumRepIso' m)
                 . liftIso _Left _Left (from oneTL)
                 . from distribR
                 . liftIso _1 _1 succFin
  {-
       Sum (Replicate (S m) a)
   ~           { def. of Replicate }
       Sum (a ': Replicate m a)
   ~           { def. of Sum }
       Either a (Sum (Replicate m a))
   <->         { IH }
       Either a (Fin m, a)
   <->         { from oneTL }
       Either ((), a) (Fin m, a)
   <->         { from distribR }
       (Either () (Fin m), a)
   <->         { succFin }
       (Fin (S m), a)
  -}

-- A variant of Proxy for type-level lists which gives us enough
-- value-level structure to pattern match on.  Similar to HVec except
-- we don't actually store any values of the given types.
data LProxy :: Nat -> [*] -> * where
  LNil  :: LProxy Z '[]
  LCons :: Proxy l -> LProxy n ls -> LProxy (S n) (l ': ls)
