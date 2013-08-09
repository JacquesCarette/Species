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
