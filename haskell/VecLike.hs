{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

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

take :: forall f l a n . Finite l => Sp f l a -> N.SNat n -> (n <= Size l) -> 
  Sp (f # Part) l a
take (Struct f i) n pf = Struct (cprodSh f (Shape k)) i
  where k :: Part l
        k = undefined
