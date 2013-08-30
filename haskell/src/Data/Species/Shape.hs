{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeOperators              #-}

module Data.Species.Shape where

import           Control.Lens
import           Data.Proxy

import           Data.BFunctor
import           Data.Fin
import           Data.Finite
import qualified Data.Set.Abstract as S
import           Data.Type.List
import           Data.Type.Nat
import qualified Data.Vec as V

import           Unsafe.Coerce

------------------------------------------------------------
--  Labelled shapes

-- Shapes with an existentially quantified label type.
data Shape' :: (* -> *) -> * where
  Shape' :: (Eq l, Finite l) => f l -> Shape' f

------------------------------------------------------------
--  Shape functors, along with introduction forms
--
-- Each introduction form gives a "canonically labeled" structure;
-- relabeling can be used to convert to some other labeling.

-- Zero ------------------------------------------

data Zero :: * -> *
  deriving Functor

instance BFunctor Zero

absurdZ :: Zero l -> a
absurdZ = unsafeCoerce

-- One -------------------------------------------

data One l = One (Fin Z <-> l)

instance Show (One l) where
  show _ = "One"

instance BFunctor One where
  bmap i = iso (\(One vl ) -> One (vl .i))
               (\(One vl') -> One (vl'.from i))

one_ :: One (Fin Z)
one_ = One id

-- X ---------------------------------------------

data X l = X (Fin (S Z) <-> l)

instance Show l => Show (X l) where
  show (X i) = show (view i FZ)

instance BFunctor X where
  bmap i = iso (\(X ul ) -> X (ul .i))
               (\(X ul') -> X (ul'.from i))

x_ :: X (Fin (S Z))
x_ = X id

-- E ---------------------------------------------

newtype E (l :: *) = E (S.Set l)
  deriving (BFunctor, Show)

e_ :: Finite l => E l
e_ = E S.enumerate

-- Sum -------------------------------------------

infixl 6 +
data (f + g) (l :: *) = Inl (f l)
                      | Inr (g l)
  deriving Functor

instance (BFunctor f, BFunctor g) => BFunctor (f + g) where
  bmap i = iso (applyIso i) (applyIso (from i))
    where
      applyIso :: (BFunctor f, BFunctor g, Finite l, Finite l')
               => (l <-> l') -> (f + g) l -> (f + g) l'
      applyIso i' (Inl f) = Inl (view (bmap i') f)
      applyIso i' (Inr g) = Inr (view (bmap i') g)

inl_ :: f l -> (f + g) l
inl_ = Inl

inr_ :: g l -> (f + g) l
inr_ = Inr

-- parallel sum? ---------------------------------

-- No idea whether this is useful for anything but it seems to be
-- suggested by parallels with linear logic.  It's dual to product
-- just as Cartesian product is dual to sum.  It's pretty weird.

data (f +? g) l where
  ParSum :: (Either (f l1) (g l2)) -> (Either l1 l2 <-> l) -> (f +? g) l

instance (BFunctor f, BFunctor g) => BFunctor (f +? g) where
  bmap i = iso (\(ParSum fg pf) -> ParSum fg (pf.i))
               (\(ParSum fg pf) -> ParSum fg (pf.from i))

pInl_ :: f l1 -> (f +? g) (Either l1 l2)
pInl_ f = ParSum (Left f) id

-- pInl :: Sp f l1 a -> Sp (f +? g) (Either l1 l2) a
-- pInl (Struct s es) = Struct (pInl_ s) (fmap Left es)

-- This doesn't typecheck because l2 is completely ambiguous.
-- Fundamentally this is because ParSum is weird.
--
-- pInl' :: Sp' f a -> Sp' (f +? g) a
-- pInl' (SpEx s) = SpEx (pInl s)

-- Product ---------------------------------------

infixl 7 *
data (f * g) l where
  Prod :: (Eq l1, Finite l1, Eq l2, Finite l2)
       => f l1 -> g l2 -> (Either l1 l2 <-> l) -> (f * g) l

instance (BFunctor f, BFunctor g) => BFunctor (f * g) where
  bmap i = iso (\(Prod f g pf) -> Prod f g (pf.i))
               (\(Prod f g pf) -> Prod f g (pf.from i))

prod_ :: (Eq l1, Finite l1, Eq l2, Finite l2)
       => f l1 -> g l2 -> (f * g) (Either l1 l2)
prod_ f g = Prod f g id

-- Cartesian product -----------------------------

data (f # g) l where
  CProd :: f l -> g l -> (f # g) l

instance (BFunctor f, BFunctor g) => BFunctor (f # g) where
  bmap i = iso (applyIso i) (applyIso (from i))
    where
      applyIso :: (BFunctor f, BFunctor g, Finite l, Finite l')
               => (l <-> l') -> (f # g) l -> (f # g) l'
      applyIso i' (CProd f g) = CProd (view (bmap i') f) (view (bmap i') g)

instance (Functor f, Functor g) => Functor (f # g) where
  fmap f (CProd f1 f2) = CProd (fmap f f1) (fmap f f2)

cprod_ :: f l -> g l -> (f # g) l
cprod_ f g = CProd f g

-- Differentiation -------------------------------

data D f l where
  D :: f l1 -> (l1 <-> Maybe l) -> D f l

instance BFunctor f => BFunctor (D f) where
  bmap i = iso (\(D f pf) -> D f (pf.iMaybe i))
               (\(D f pf) -> D f (pf.iMaybe (from i)))

iMaybe :: (a <-> b) -> (Maybe a <-> Maybe b)
iMaybe i = liftIso _Just _Just i

d_ :: f (Maybe l) -> (D f) l
d_ f = D f id

-- Pointing --------------------------------------

data P f l where
  P :: l -> f l -> P f l

instance BFunctor f => BFunctor (P f) where
  bmap i = iso (\(P l f) -> P (view i l) (view (bmap i) f))
               (\(P l f) -> P (view (from i) l) (view (bmap (from i)) f))

p_ :: l -> f l -> (P f) l
p_ l f = P l f

-- Partition   -----------------------------------
-- This can be see as 'just' E * E, but it is useful to give it a name

data Part l where
  Part :: (Finite l1, Finite l2) => S.Set l1 -> S.Set l2 -> (Either l1 l2 <-> l) -> Part l

instance BFunctor Part where
  bmap i = iso (\(Part s1 s2 pf) -> Part s1 s2 (pf.i))
               (\(Part s1 s2 pf) -> Part s1 s2 (pf.from i))

part_ :: (Finite l1, Finite l2) => (Either l1 l2 <-> l) -> Part l
part_ i = Part S.enumerate S.enumerate i

-- Composition -----------------------------------

data Comp f g l where
  Comp :: Eq l1
       => f l1
       -> LProxy (Size l1) ls
       -> V.HVec (Size l1) (Map g ls)
       -> (Sum ls <-> l)
       -> Comp f g l

instance BFunctor f => BFunctor (Comp f g) where
  bmap i = iso (\(Comp fl lp gs pf) -> Comp fl lp gs (pf.i))
               (\(Comp fl lp gs pf) -> Comp fl lp gs (pf.from i))


-- Cardinality restriction -----------------------

data OfSize :: Nat -> (* -> *) -> * -> * where
  OfSize :: SNat n -> (Fin n <-> l) -> f l -> OfSize n f l

instance BFunctor f => BFunctor (OfSize n f) where
  bmap i = iso (\(OfSize n eq f) -> OfSize n (eq.i) (view (bmap i) f))
               (\(OfSize n eq f) -> OfSize n (eq.from i) (view (bmap (from i)) f))

sized_ :: forall f l. Finite l => f l -> (OfSize (Size l) f) l
sized_ sh = OfSize (size (Proxy :: Proxy l)) finite sh

