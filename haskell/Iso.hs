{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeOperators #-}

module Iso where

import Control.Category
import Data.Functor ((<$>))
import Prelude hiding ((.), id)

data l1 <-> l2 = Iso { there :: l1 -> l2, back :: l2 -> l1 }

instance Category (<->) where
  id = Iso id id
  (Iso f f') . (Iso g g') = Iso (f . g) (g' . f')

inv :: (a <-> b) -> (b <-> a)
inv (Iso f g) = Iso g f

class BFunctor f where
  bmap :: (a <-> b) -> (f a <-> f b)

  default bmap :: Functor f => (a <-> b) -> (f a <-> f b)
  bmap iso = Iso (there iso <$>) (back iso <$>)

