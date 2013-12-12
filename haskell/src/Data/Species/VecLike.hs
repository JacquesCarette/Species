{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

------------------------------------------
-- The point of this module is to show that many vector operations
-- can be defined generally on species

module Data.Species.VecLike where

import           Control.Lens
import           Data.Proxy
import           Data.Type.Equality

import qualified Data.Fin                 as F
import           Data.Fin.Isos
import           Data.Iso
import           Data.Finite
import qualified Data.Set.Abstract        as S
import           Data.Species.Shape
import           Data.Species.Types
import qualified Data.Type.Nat            as N
import           Data.Type.Nat.Inequality
import           Data.Type.Nat.Minus
import qualified Data.Vec                 as V

{-
   This fails, as it REQUIRES l ~ F.Fin (N.Plus n j))

take :: forall f l a n . HasSize l => Sp f l a -> N.SNat n -> (n <= Size l) ->
  Sp (f # Part) l a
take (Struct f i finl) n pf =
  case minus (size finl) n pf of
    Minus (m :: N.SNat m) Refl ->
      case N.plusComm m n of
        Refl -> Struct (cprod_ f k) i finl
          where k :: Part l
                k = N.natty n $ N.natty m $ Part (S.enumerate finite_Fin) (S.enumerate finite_Fin) isom
                isom :: Either (F.Fin n) (F.Fin m) <-> l
                isom = iso (finSum n m) (finSum' n m)
-}

-- This works, but because it relies on knowing a specific label set iso:
take :: forall f a q n. N.Natural q => Sp f s (F.Fin q) a -> N.SNat n -> (n <= q) ->
  Sp (f # Part) s (F.Fin q) a
take (Struct f i finq) n pf =
  case minus (size finq) n pf of
    Minus (m :: N.SNat m) Refl ->
      case N.plusComm m n of
        Refl -> Struct (cprod_ f k) i finq
          where k :: Part (F.Fin q)
                k = N.natty n $ N.natty m $ Part (S.enumerate finite_Fin) (S.enumerate finite_Fin) isom
                isom :: Either (F.Fin n) (F.Fin m) <-> F.Fin q
                isom = iso (finSum n m) (finSum' n m)
data VPart l where
  VPart :: V.Vec n l -> V.Vec m l -> N.Plus n m :=: Size l -> VPart l

vpart :: V.Vec n Bool -> VPart (F.Fin n)
vpart V.VNil = VPart V.VNil V.VNil Refl
vpart (V.VCons a v) = case vpart v of
  VPart ns ms Refl ->
    if a then VPart (V.VCons F.FZ (fmap F.FS ns)) (fmap F.FS ms) Refl
         else VPart (fmap F.FS ns) (V.VCons F.FZ (fmap F.FS ms))
                    (case N.plusSuccR (V.size ns) (V.size ms) of Refl -> Refl)

{- This is still not right
filter :: forall f l a. Sp f s l a -> (a -> Bool) -> Sp (f # Part) s l a
filter (Struct f i finl@(F isof)) p =
  let foo = fmap p i in
  case vpart foo of
    VPart (v1 :: V.Vec n (F.Fin (Size l))) (v2 :: V.Vec m (F.Fin (Size l))) Refl
      -> Struct (cprod_ f k) i finl
        where k :: Part l
              k = N.natty (V.size v1) $ N.natty (V.size v2) $
                  Part (S.enumerate finite_Fin) (S.enumerate finite_Fin) isom
              isom :: Either (F.Fin n) (F.Fin m) <-> l
              isom = iso foo bar
              foo :: Either (F.Fin n) (F.Fin m) -> l
              foo (Left n) = V.index v1 n
              foo (Right m) = V.index v2 m
              bar l = case V.lookup v1 (view finl l) of
                        Just n1 -> Left n1
                        Nothing -> case V.lookup v2 l of
                                      Just m1 -> Right m1
                                      Nothing -> error "this case cannot happen"
-}
