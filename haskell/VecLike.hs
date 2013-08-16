{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

------------------------------------------
-- The point of this module is to show that many vector operations
-- can be defined generally on species

module VecLike where

import SpeciesTypes
import qualified Nat as N
import Finite
import qualified Vec as V
import FinIsos
import Control.Lens
import qualified Set as S
import Proxy
import Equality

natty :: N.SNat n -> (N.Natural n => r) -> r
natty N.SZ r     = r
natty (N.SS n) r = natty n r

take :: forall f l a n . (Finite l) => Sp f l a -> N.SNat n -> (n <= Size l) -> 
  Sp (f # Part) l a
take (Struct f i) n pf = 
  case minus (size (Proxy :: Proxy l)) n pf of
    Minus (m :: N.SNat m) Refl -> 
      case plusComm m n of 
        Refl -> Struct (cprodSh f (Shape k)) i
          where k :: Part l
                k = natty n $ natty m $ Part S.enumerate S.enumerate isom
                isom :: Either (N.Fin n) (N.Fin m) <-> l
                isom = iso (finSum n m) (finSumInv n m) . finite

data VPart l where
  VPart :: V.Vec n l -> V.Vec m l -> N.Plus n m == Size l -> VPart l
  
vpart :: V.Vec n Bool -> VPart (N.Fin n)
vpart V.VNil = VPart V.VNil V.VNil Refl
vpart (V.VCons a v) = case vpart v of
  VPart ns ms Refl ->
    if a then VPart (V.VCons N.FZ (fmap N.FS ns)) (fmap N.FS ms) Refl
         else VPart (fmap N.FS ns) (V.VCons N.FZ (fmap N.FS ms)) 
                    (case plusSuccR (V.vSize ns) (V.vSize ms) of Refl -> Refl)


filter :: forall f l a. Finite l => Sp f l a -> (a -> Bool) -> Sp (f # Part) l a
filter (Struct f i) p =
  let foo = fmap p i in
  case vpart foo of 
    VPart (v1 :: V.Vec n (N.Fin (Size l))) (v2 :: V.Vec m (N.Fin (Size l))) Refl 
      -> Struct (cprodSh f (Shape k)) i
        where k :: Part l
              k = natty (V.vSize v1) $ natty (V.vSize v2) $ 
                  Part S.enumerate S.enumerate isom
              isom :: Either (N.Fin n) (N.Fin m) <-> l
              isom = iso foo bar
              foo (Left n) = V.vIndex v1' n
              foo (Right m) = V.vIndex v2' m           
              bar l = case V.vLookup v1 (view (from finite) l) of
                        Just n1 -> Left n1
                        Nothing -> case V.vLookup v2 (view (from finite) l) of
                                      Just m1 -> Right m1
                                      Nothing -> error "this case cannot happen"
              v1' = fmap (view finite) v1
              v2' = fmap (view finite) v2

