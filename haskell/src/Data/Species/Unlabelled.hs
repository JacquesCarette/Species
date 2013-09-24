{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}

module Data.Species.Unlabelled where

import           Control.Lens
import qualified Data.Foldable      as F
import qualified Data.Key           as K
import           Data.Maybe         (fromJust)
import           Data.Tuple         (swap)

import           Data.Finite
import           Data.Species.Types
import qualified Data.Vec           as V

newtype USp f l a = USp { _usp :: Sp f l a }

makeLenses ''USp

-- Not sure whether this is useful/a good idea.  The idea here is that
-- you can zip two labelled structures which are really just
-- representatives of equivalence classes.  As a result you get an
-- output structure as well as the correspondence between their
-- label types.
zipU :: (K.Zip f, F.Foldable f, Size l1 ~ Size l2, Eq l1, Eq l2)
     => (a -> b -> c) -> USp f l1 a -> USp f l2 b -> (USp f l1 c, l1 <-> l2)
zipU f (USp (Struct fl1 es1 finl1)) (USp (Struct fl2 es2 finl2))
  = ( USp (Struct fl1 (V.zipWith f es1 es2) finl1)
    , iso (fromJust . (lookup ?? ls)) (fromJust . (lookup ?? map swap ls))
    )
  where
    ls = F.foldMap (:[]) (K.zip fl1 fl2)
