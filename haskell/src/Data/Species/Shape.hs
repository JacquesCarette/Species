{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeOperators              #-}

-- | This module defines a number of primitive species and species
--   operations which are used as the basis for constructing labelled
--   shapes.
--
--   Each species comes with one or more introduction forms, which
--   gives a \"canonically labelled\" shape; relabelling can be used
--   to convert to some other labelling.
module Data.Species.Shape
    ( -- * Labelled shapes
      -- $labshapes

      Shape'(..)

      -- * Zero
    , Zero, absurdZ

      -- * One
    , One(..), one_

      -- * X
    , X(..), x_

      -- * E
    , E(..), e_

      -- * Sum
    , (+)(..), inl_, inr_

      -- * Product
    , (*)(..), prod_

      -- * Cartesian product
    , (#)(..), cprod_

      -- * Differentiation
    , D(..), d_

      -- * Pointing
    , P(..), p_

      -- * Partition
    , Part(..), part_

      -- * Composition
    , Comp(..)

      -- * Functor composition
    , FComp(..), fcomp_

      -- * Cardinality restriction
    , OfSize(..), sized_
    )
    where

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

-- $labshapes
-- Note that there is no separate distinguished type to represent
-- labelled shapes: labelled shapes are simply values of type @f l@
-- for some suitable shape constructor (/i.e./ species) @f@ and label
-- type @l@.
--
-- On the other hand, we do have the below type 'Shape'' for
-- existentially hiding the label type of a shape.

-- | Shapes with an existentially quantified label type.
data Shape' :: (* -> *) -> * where
  Shape' :: (Eq l, Finite l) => f l -> Shape' f

------------------------------------------------------------
--  Shape functors, along with introduction forms
--

-- Zero ------------------------------------------

-- | The void species.  There are no values of shape @Zero@, /i.e./ it
--   has no introduction forms.
data Zero :: * -> *
  deriving Functor

instance BFunctor Zero

-- | We provide an elimination form for @Zero@ shapes, corresponding
--   to /ex falso quodlibet/.
absurdZ :: Zero l -> a
absurdZ = unsafeCoerce

-- One -------------------------------------------

-- | The unit species, with only a single shape of size zero.
data One l = One (Fin Z <-> l)

instance Show (One l) where
  show _ = "One"

instance BFunctor One where
  bmap i = iso (\(One vl ) -> One (vl .i))
               (\(One vl') -> One (vl'.from i))

-- | Trivial introduction form for the canonical @One@-shape.
one_ :: One (Fin Z)
one_ = One id

-- X ---------------------------------------------

-- | The \"singleton\" species, which has a single shape of size
--   one.
data X l = X (Fin (S Z) <-> l)

instance Show l => Show (X l) where
  show (X i) = show (view i FZ)

instance BFunctor X where
  bmap i = iso (\(X ul ) -> X (ul .i))
               (\(X ul') -> X (ul'.from i))

-- | Trivial introduction form for the canonical @X@-shape.
x_ :: X (Fin (S Z))
x_ = X id

-- E ---------------------------------------------

-- | The species of bags, with one shape of each size.
newtype E (l :: *) = E (S.Set l)
  deriving (BFunctor, Show)

-- | Trivial introduction form for the canonical @E@-shape of any set
--   of labels.
e_ :: Finite l => E l
e_ = E S.enumerate

-- Sum -------------------------------------------

infixl 6 +

-- | Species sum, /i.e./ disjoint union.
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

-- | Inject an @f@-shape into an @(f+g)@-shape.
inl_ :: f l -> (f + g) l
inl_ = Inl

-- | Inject a @g@-shape into an @(f+g)@-shape.
inr_ :: g l -> (f + g) l
inr_ = Inr

-- Product ---------------------------------------

infixl 7 *

-- | Species product, /i.e./ partitional product.  A labelled @(f *
--   g)@-shape partitions the set of labels between the @f@-shape and
--   the @g@-shape.
data (f * g) l where
  Prod :: (Eq l1, Finite l1, Eq l2, Finite l2)
       => f l1 -> g l2 -> (Either l1 l2 <-> l) -> (f * g) l

instance (BFunctor f, BFunctor g) => BFunctor (f * g) where
  bmap i = iso (\(Prod f g pf) -> Prod f g (pf.i))
               (\(Prod f g pf) -> Prod f g (pf.from i))

-- | Introduction form for making an @(f * g)@-shape by pairing an
--   @f@-shape and a @g@-shape.  The resulting set of labels is the
--   disjoin union of those used for the @f@- and @g@-shapes.
prod_ :: (Eq l1, Finite l1, Eq l2, Finite l2)
       => f l1 -> g l2 -> (f * g) (Either l1 l2)
prod_ f g = Prod f g id

-- Cartesian product -----------------------------

-- | Cartesian product.  A labelled @(f # g)@-shape duplicates the set
--   of labels to both the @f@-shape and the @g@-shape.
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

-- | Introduction form for @(f # g)@-shapes.
cprod_ :: f l -> g l -> (f # g) l
cprod_ f g = CProd f g

-- Differentiation -------------------------------

-- | The differentiation operator on species.  A @(D f)@-shape can be
--   thought of intuitively as an @f@-shape with a \"hole\".
data D f l where
  D :: f l1 -> (l1 <-> Maybe l) -> D f l

instance BFunctor f => BFunctor (D f) where
  bmap i = iso (\(D f pf) -> D f (pf.iMaybe i))
               (\(D f pf) -> D f (pf.iMaybe (from i)))

iMaybe :: (a <-> b) -> (Maybe a <-> Maybe b)
iMaybe i = liftIso _Just _Just i

-- | Introduction form for @D@.  The \"hole\" is indicated by
--   @Nothing@.
d_ :: f (Maybe l) -> (D f) l
d_ f = D f id

-- Pointing --------------------------------------

-- | The pointing operator on species.  A @(P f)@-shape is an @f@-shape
--   with a distinguished label.
data P f l where
  P :: l -> f l -> P f l

instance BFunctor f => BFunctor (P f) where
  bmap i = iso (\(P l f) -> P (view i l) (view (bmap i) f))
               (\(P l f) -> P (view (from i) l) (view (bmap (from i)) f))

-- | Introduction form for @P@.
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

-- | The (partitional) composition of species. A labelled @(Comp f
--   g)@-shape is intuitively an @f@-shape of @g@-shapes, with the
--   labels distributed among all the @g@-shapes.
--
--   No introduction forms for @Comp@-shapes are given; instead, see
--   "Data.Species.Types" for several introduction forms for @Comp@
--   structures (/i.e./ shape + data).
data Comp f g l where
  Comp :: (Eq l1, Finite l1, All Eq ls)
       => f l1
       -> LProxy (Size l1) ls
       -> V.HVec (Size l1) (Map g ls)
       -> (Sum ls <-> l)
       -> Comp f g l

instance BFunctor f => BFunctor (Comp f g) where
  bmap i = iso (\(Comp fl lp gs pf) -> Comp fl lp gs (pf.i))
               (\(Comp fl lp gs pf) -> Comp fl lp gs (pf.from i))

-- Cardinality restriction -----------------------

-- | Cardinality restriction.  @(OfSize n f)@-shapes are @f@-shapes of
--   size exactly @n@.
data OfSize :: Nat -> (* -> *) -> * -> * where
  OfSize :: SNat n -> (Fin n <-> l) -> f l -> OfSize n f l

instance BFunctor f => BFunctor (OfSize n f) where
  bmap i = iso (\(OfSize n eq f) -> OfSize n (eq.i) (view (bmap i) f))
               (\(OfSize n eq f) -> OfSize n (eq.from i) (view (bmap (from i)) f))

-- | Introduction form for cardinality restriction.
sized_ :: forall f l. Finite l => f l -> (OfSize (Size l) f) l
sized_ sh = OfSize (size (Proxy :: Proxy l)) finite sh

-- Functor composition --------------------------

-- | Functor composition. XXX write more.
data FComp f g l = FComp (f (g l))

-- | Introduction form for functor composition.  XXX more.
fcomp_
  :: (BFunctor f, Finite l1, Finite (g l2))
  => f l1 -> (l1 <-> g l2) -> FComp f g l2
fcomp_ f g = FComp (view (bmap g) f)

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

