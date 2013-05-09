{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs          #-}

import           Prelude hiding ((.), id)

import           Control.Category
import           Control.Lens
import qualified Data.Map as M
import           Data.Void

data Sp f l a = Struct { _size  :: Int
                       , _shape :: f l
                       , _elts  :: l -> a
                       }

makeLenses ''Sp

instance Functor (Sp f l) where
  fmap h (Struct sz shp elts) = Struct sz shp (h . elts)

data Sh f l where
  Shape :: Int -> f l -> Sh f l

data l1 <-> l2 = Iso { there :: l1 -> l2, back :: l2 -> l1 }

instance Category (<->) where
  id = Iso id id
  (Iso f f') . (Iso g g') = Iso (f . g) (g' . f')

inv :: (a <-> b) -> (b <-> a)
inv (Iso f g) = Iso g f

class BFunctor f where
  bmap :: (a <-> b) -> (f a <-> f b)

  default bmap :: Functor f => (a <-> b) -> (f a <-> f b)
  bmap iso = Iso (fmap (there iso)) (fmap (back iso))

relabel :: BFunctor f => (l1 <-> l2) -> (Sp f l1 a <-> Sp f l2 a)
relabel s = Iso
  { there = \(Struct sz shp elts) -> Struct sz (there (bmap s) shp) (elts . back s)
  , back  = \(Struct sz shp elts) -> Struct sz (back (bmap s) shp)  (elts . there s)
  }
  -- XXX the above would be much nicer with some... lenses =)

reshape :: (f l -> g l) -> (Sp f l a -> Sp g l a)
reshape r (Struct sz shp elts) = Struct sz (r shp) elts

data O l deriving Functor
instance BFunctor O

data I l = I (Void <-> l)

instance BFunctor I where
  bmap iso = Iso (\(I isoV) -> I (isoV >>> iso))
                 (\(I isoV) -> I (isoV >>> inv iso))

data X l = X () (() <-> l)

instance BFunctor X where
  bmap iso = Iso (\(X () isoU) -> X () (isoU >>> iso))
                 (\(X () isoU) -> X () (isoU >>> inv iso))

data E l = E deriving Functor
instance BFunctor E

data (f + g) l where
  InL :: f l1 -> (l1 <-> l) -> (f + g) l
  InR :: g l2 -> (l2 <-> l) -> (f + g) l

instance (BFunctor f, BFunctor g) => BFunctor (f + g) where
  bmap iso = Iso therePlus backPlus
    where therePlus (InL x iso1) = InL x (iso1 >>> iso)
          therePlus (InR x iso2) = InR x (iso2 >>> iso)
          backPlus  (InL x iso1) = InL x (iso1 >>> inv iso)
          backPlus  (InR x iso2) = InR x (iso2 >>> inv iso)

data (f * g) l where
  Prod :: f l1 -> g l2 -> (Either l1 l2 <-> l) -> (f * g) l

instance (BFunctor f, BFunctor g) => BFunctor (f * g) where
  bmap iso = Iso (\(Prod x y isoE) -> Prod x y (isoE >>> iso))
                 (\(Prod x y isoE) -> Prod x y (isoE >>> inv iso))

data (f & g) l = Cart (f l) (g l)

data (f :. g) l where
  Comp :: f l1 -> (l1 -> g l2) -> ((l1,l2) <-> l) -> (f :. g) l

data Deriv f l where
  D :: f l1 -> (l1 <-> Maybe l) -> Deriv f l

type Pointed f = (X * Deriv f)

class Pointable f where
  point :: Sp f l a -> Sp (Pointed f) l a

instance Pointable O where
  point = undefined  -- Sp O l a  and  Sp (Pointed O) l a are both uninhabited

-- instance Pointable I where
--   point = reshape undefined
-- argh

instance Pointable X where
  point = reshape (\(X l lU) -> (Prod (X () id) (D (X () id) (inv maybeZero)) (onePlusZero >>> lU)))

onePlusZero :: Either () Void <-> ()
onePlusZero = undefined

maybeZero :: Maybe Void <-> ()
maybeZero = undefined

instance (IsZero f, Pointable f, Pointable g) => Pointable (f + g) where
  point = undefined

class IsZero f where
  isZero :: f l -> Bool

instance IsZero O where
  isZero = const True

instance IsZero I where
  isZero = const False

instance IsZero X where
  isZero = const False

instance (IsZero f, IsZero g) => IsZero (f + g) where
  isZero (InL x _) = isZero x
  isZero (InR x _) = isZero x

instance (IsZero f, IsZero g) => IsZero (f * g) where
  isZero (Prod x y _) = isZero x || isZero y

{-
class Holey f where
  labels :: f l -> [l]

instance Holey O where
  labels = undefined

instance Holey I where
  labels = const []

instance Holey X where
  labels (X l) = [l]

instance Holey E where
  labels = undefined   -- ???  need a constraint on l -- i.e. enumerate the labels

instance (Holey f, Holey g) => Holey (f + g) where
  labels (InL fl) = labels fl
  labels (InR gl) = labels gl

instance (Holey f, Holey g) => Holey (f * g) where
  labels (Prod fl gl) = map Left (labels fl) ++ map Right (labels gl)

instance (Holey f) => Holey (f & g) where
  labels (Cart fl _) = labels fl

instance (Holey f, Holey g) => Holey (f :. g) where
  labels (Comp fl gls) = do
    l1 <- labels fl
    l2 <- labels (gls l1)
    return (l1,l2)

one :: Sp I Void a
one = Struct 0 I absurd

x :: a -> Sp X () a
x a = Struct 1 (X ()) (const a)

bag :: [a] -> Sp E Int a
bag as = Struct (length as) E (M.fromList (zip [0..] as) M.!)

inl :: Sp f l a -> Sp (f + g) l a
inl (Struct sz shp elts) = Struct sz (InL shp) elts

inr :: Sp g l a -> Sp (f + g) l a
inr (Struct sz shp elts) = Struct sz (InR shp) elts

(*~) :: Sp f l1 a -> Sp g l2 a -> Sp (f*g) (Either l1 l2) a
(Struct sz1 shp1 elts1) *~ (Struct sz2 shp2 elts2)
  = Struct
      (sz1+sz2)
      (Prod shp1 shp2)
      (either elts1 elts2)

comp :: Holey f => Sh f l1 -> (l1 -> Sp g l2 a) -> Sp (f :. g) (l1,l2) a
comp (Shape n s) m = Struct n' (Comp s (shape . m)) m'
  where
    n' = undefined
    m' = undefined
    ls = labels s

-- XXX existentially quantify over label types at some point?  should
-- all still work I think.

-}
