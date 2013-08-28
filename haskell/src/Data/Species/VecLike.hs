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
import qualified Data.Fin                 as F
import           Data.Fin.Isos
import           Data.Finite
import           Data.Proxy
import qualified Data.Set.Abstract        as S
import           Data.Species.Types
import           Data.Type.Equality
import qualified Data.Type.Nat            as N
import           Data.Type.Nat.Inequality
import           Data.Type.Nat.Minus
import qualified Data.Vec                 as V

natty :: N.SNat n -> (N.Natural n => r) -> r
natty N.SZ r     = r
natty (N.SS n) r = natty n r

take :: forall f l a n . (Finite l) => Sp f l a -> N.SNat n -> (n <= Size l) ->
  Sp (f # Part) l a
take (Struct f i) n pf =
  case minus (size (Proxy :: Proxy l)) n pf of
    Minus (m :: N.SNat m) Refl ->
      case N.plusComm m n of
        Refl -> Struct (cprodSh f k) i
          where k :: Part l
                k = natty n $ natty m $ Part S.enumerate S.enumerate isom
                isom :: Either (F.Fin n) (F.Fin m) <-> l
                isom = iso (finSum n m) (finSumInv n m) . finite

data VPart l where
  VPart :: V.Vec n l -> V.Vec m l -> N.Plus n m :=: Size l -> VPart l

vpart :: V.Vec n Bool -> VPart (F.Fin n)
vpart V.VNil = VPart V.VNil V.VNil Refl
vpart (V.VCons a v) = case vpart v of
  VPart ns ms Refl ->
    if a then VPart (V.VCons F.FZ (fmap F.FS ns)) (fmap F.FS ms) Refl
         else VPart (fmap F.FS ns) (V.VCons F.FZ (fmap F.FS ms))
                    (case N.plusSuccR (V.size ns) (V.size ms) of Refl -> Refl)


filter :: forall f l a. Finite l => Sp f l a -> (a -> Bool) -> Sp (f # Part) l a
filter (Struct f i) p =
  let foo = fmap p i in
  case vpart foo of
    VPart (v1 :: V.Vec n (F.Fin (Size l))) (v2 :: V.Vec m (F.Fin (Size l))) Refl
      -> Struct (cprodSh f k) i
        where k :: Part l
              k = natty (V.size v1) $ natty (V.size v2) $
                  Part S.enumerate S.enumerate isom
              isom :: Either (F.Fin n) (F.Fin m) <-> l
              isom = iso foo bar
              foo (Left n) = V.index v1' n
              foo (Right m) = V.index v2' m
              bar l = case V.lookup v1 (view (from finite) l) of
                        Just n1 -> Left n1
                        Nothing -> case V.lookup v2 (view (from finite) l) of
                                      Just m1 -> Right m1
                                      Nothing -> error "this case cannot happen"
              v1' = fmap (view finite) v1
              v2' = fmap (view finite) v2
