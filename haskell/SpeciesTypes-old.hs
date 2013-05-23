{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs          #-}

import           Prelude hiding ((.), id)

import           Control.Arrow ((&&&))
import           Control.Category
import           Data.Functor ((<$>))
import           Data.Functor.Constant
import           Data.Functor.Coproduct
import           Data.Functor.Identity
import           Data.Functor.Product
import           Iso
-- import           Control.Lens
import qualified TMap as M
import           Data.Void

import qualified Set as S

data Sp f l a = Struct { size  :: Int
                       , shape :: f l
                       , elts  :: M.Map l a
                       }

-- makeLenses ''Sp

instance Functor (Sp f l) where
  fmap h (Struct sz shp elts) = Struct sz shp (h <$> elts)

data Sh f l where
  Shape :: Int -> f l -> Sh f l

relabel :: BFunctor f => (l1 <-> l2) -> (Sp f l1 a <-> Sp f l2 a)
relabel s = Iso
  { there = \(Struct sz shp elts) -> Struct sz (there (bmap s) shp) (M.mapLabels s elts)
  , back  = \(Struct sz shp elts) -> Struct sz (back (bmap s) shp)  (M.mapLabels (inv s) elts)
  }
  -- XXX the above would be much nicer with some... lenses =)

reshape :: (f l -> g l) -> (Sp f l a -> Sp g l a)
reshape r (Struct sz shp elts) = Struct sz (r shp) elts

data O (l :: *) deriving Functor
instance BFunctor O

data I l = I (Void <-> l)

instance BFunctor I where
  bmap iso = Iso (\(I isoV) -> I (isoV >>> iso))
                 (\(I isoV) -> I (isoV >>> inv iso))

data X l = X () (() <-> l)

instance BFunctor X where
  bmap iso = Iso (\(X l isoU) -> X l (isoU >>> iso))
                 (\(X l isoU) -> X l (isoU >>> inv iso))

data E l = E (S.Set l) deriving Functor
instance BFunctor E

data (f + g) l where
  InL :: Eq l1 => f l1 -> (l1 <-> l) -> (f + g) l
  InR :: Eq l2 => g l2 -> (l2 <-> l) -> (f + g) l

instance (BFunctor f, BFunctor g) => BFunctor (f + g) where
  bmap iso = Iso therePlus backPlus
    where therePlus (InL x iso1) = InL x (iso1 >>> iso)
          therePlus (InR x iso2) = InR x (iso2 >>> iso)
          backPlus  (InL x iso1) = InL x (iso1 >>> inv iso)
          backPlus  (InR x iso2) = InR x (iso2 >>> inv iso)

data (f * g) l where
  Prod :: (Eq l1, Eq l2) => f l1 -> g l2 -> (Either l1 l2 <-> l) -> (f * g) l

instance (BFunctor f, BFunctor g) => BFunctor (f * g) where
  bmap iso = Iso (\(Prod x y isoE) -> Prod x y (isoE >>> iso))
                 (\(Prod x y isoE) -> Prod x y (isoE >>> inv iso))

data (f & g) l = Cart (f l) (g l)

data (f :. g) l where
  Comp :: (Eq l1, Eq l2) => f l1 -> (l1 -> g l2) -> ((l1,l2) <-> l) -> (f :. g) l

comp :: (Holey f, Eq l1, Eq l2) => Sh f l1 -> (l1 -> Sp g l2 a) -> Sp (f :. g) (l1,l2) a
comp (Shape n s) m = Struct n' (Comp s (shape . m) id) m'
  where
    n' = S.sum $ fmap (size . m) ls
    m' = foo $ fmap (id &&& (elts . m)) ls
    ls = labels s

    foo :: S.Set (l1, M.Map l2 a) -> M.Map (l1,l2) a
    foo b = undefined

data Deriv f l where
  D :: f l1 -> (l1 <-> Maybe l) -> Deriv f l

data Pointed f l = Pointed (f l) l

class Pointable f where
  point :: Sp f l a -> Sp (Pointed f) l a

instance Pointable X where
  point = reshape (\x@(X l lU) -> (Pointed x (there lU l)))

-- instance (Pointable f, Pointable g) => Pointable (f+g) where
--   point = reshape r
--     where
--       r (InL f iso) = Pointed (InL f)

class Holey f where
  labels :: Eq l => f l -> S.Set l

instance Holey O where
  labels = undefined

instance Holey I where
  labels = const S.empty

instance Holey X where
  labels (X l iso) = S.singleton (there iso l)

instance Holey E where
  labels (E ls) = ls

instance (Holey f, Holey g) => Holey (f + g) where
  labels (InL fl iso) = fmap (there iso) (labels fl)
  labels (InR gl iso) = fmap (there iso) (labels gl)

instance (Holey f, Holey g) => Holey (f * g) where
  labels (Prod fl gl iso) = fmap (there iso)
                          $ fmap Left (labels fl) `S.union` fmap Right (labels gl)

instance (Holey f) => Holey (f & g) where
  labels (Cart fl _) = labels fl

instance (Holey f, Holey g) => Holey (f :. g) where
  labels (Comp fl gls iso) = do
    l1 <- labels fl
    l2 <- labels (gls l1)
    return (there iso (l1,l2))

one :: Sp I Void a
one = Struct 0 (I id) M.empty

x :: a -> Sp X () a
x a = Struct 1 (X () id) (M.singleton a)

{-

bag :: [a] -> Sp E Int a
bag as = Struct (length as) E (M.fromList (zip [0..] as) M.!)

-}

inl :: Eq l => Sp f l a -> Sp (f + g) l a
inl (Struct sz shp elts) = Struct sz (InL shp id) elts

inr :: Eq l => Sp g l a -> Sp (f + g) l a
inr (Struct sz shp elts) = Struct sz (InR shp id) elts

(*~) :: (Eq l1, Eq l2) => Sp f l1 a -> Sp g l2 a -> Sp (f*g) (Either l1 l2) a
(Struct sz1 shp1 elts1) *~ (Struct sz2 shp2 elts2)
  = Struct
      (sz1+sz2)
      (Prod shp1 shp2 id)
      un -- XXX FIXME (either elts1 elts2)

pr :: Sp (X * X) Bool Int
pr = there (relabel onePlusOneBool) $ x 3 *~ x 4

onePlusOneBool :: Either () () <-> Bool
onePlusOneBool = Iso (either (const False) (const True)) (\b -> (if b then Right else Left) ())

-- XXX existentially quantify over label types at some point?  should
-- all still work I think.

class Viewable f where
  type View f :: * -> *
  view' :: Eq l => f l -> M.Map l a -> View f a

view :: (Eq l, Viewable f) => Sp f l a -> View f a
view (Struct _ s elts) = view' s elts

instance Viewable O where
  type View O = Constant Void
  view' z _ = undefined  -- z cannot exist

instance Viewable I where
  type View I = Constant ()
  view' _ _ = Constant ()

instance Viewable X where
  type View X = Identity
  view' (X _ lU) elts = Identity (M.lookup (there lU ()) elts)

instance (Viewable f, Viewable g) => Viewable (f + g) where
  type View (f+g) = Coproduct (View f) (View g)
  view' (InL x pf) elts = Coproduct (Left (view' x (M.mapLabels (inv pf) elts)))
  view' (InR x pf) elts = Coproduct (Right (view' x (M.mapLabels (inv pf) elts)))

instance (Viewable f, Viewable g) => Viewable (f * g) where
  type View (f*g) = Product (View f) (View g)
  view' (Prod x y pf) elts = Pair (view' x elts1) (view' y elts2)
    where (elts1, elts2) = M.unUnion $ M.mapLabels (inv pf) elts

------------------------------------------------------------
-- Recursion!

data Mu :: (* -> * -> *) -> * -> * where
  Mu :: f y l'
        -- Top-level f structure, with labels of type y marking
        -- occurrences of recursive substructures, and labels of type
        -- l' marking atoms

     -> SNat n
        -- Number of recursive substructures

     -> (y <-> Fin n)
        -- Proof that y is an n-element label set

     -> Proxy ls
        -- Hack to allow instantiating the type ls

     -> Substructures f n ls
        -- List of n recursive substructures, each using the
        -- respective label type in the list of types ls :: [*].

     -> (Either l' (Sum ls) <-> l)
        -- The type of labels for the overall structure is the sum of
        -- the label types used in the top-level structure and all the
        -- recursive substructures.

     -> Mu f l

data Proxy a = Proxy

type family Sum (xs :: [*]) :: *
type instance Sum '[]       = Zero
type instance Sum (x ': xs) = Either x (Sum xs)

-- for now, ls :: '[*], though it should really have kind 'Vec n * .
-- But for that we need to be able to promote GADTs.

type family Substructures (f :: * -> * -> *) (n :: Nat) (ls :: [*]) :: *
type instance Substructures f Z '[] = ()
type instance Substructures f (S n) (l ': ls) = (Mu f l, Substructures f n ls)

data Ref y l = Ref y

data Nat = Z | S Nat

data SNat :: Nat -> * where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

data Fin :: Nat -> * where
  FZ :: Fin (S n)
  FS :: Fin n -> Fin (S n)

type Zero = Void
type One = Fin (S Z)
type Two = Fin (S (S Z))
type Three = Fin (S (S (S Z)))

un = undefined

{-  XXX working here: project out recursive structures

instance (ViewableF f) => Viewable (Mu f) where

class ViewableF f where
  viewF ::
-}

------------------------------------------------------------
-- Binary tree example

data T :: * -> * -> * where
  T :: (X + (Ref y * Ref y)) l -> T y l

type Tree = Mu T

tree :: Sp Tree Two Char
tree = Struct
  2
  (Mu
    (T (InR (Prod (Ref FZ) (Ref (FS FZ)) zeroPlus) id))
    (SS (SS SZ))
    id
    (Proxy :: Proxy [One,One])
    (sub,(sub,()))
    (zeroPlus >>> onePlusOne)
  )
  un
--  (M.toMap [(Left (), 'x'), (Right (Left ()), 'y')])
  where
    sub :: Mu T One
    sub = Mu (T (InL (X () (inv zeroPlus)) id)) SZ id (Proxy :: Proxy '[]) ()
            (plusZero >>> zeroPlus >>> unitOne)

{-
data family T1 (ys :: [*]) :: * -> *
data instance T1 ys l = T1 ((X * Ref (ys !! S Z)) l)

data family T2 (ys :: [*]) :: * -> *
data instance T2 ys l = T2 ((X * X * Ref (ys !! Z)) l)

type Foo = Mu T1 [T1,T2] [(),()]


foo :: Sp Foo Three Int
foo = Struct 3 (Mu (T1 (Prod (X () id) (Ref ()) id)) () assoc)
  (M.toMap [(Left (), 16), (Right (Left ()), 99), (Right (Right (Left ())), 4)])
-}

plusAssoc :: Either (Either a b) c <-> Either a (Either b c)
plusAssoc = Iso assocR assocL
  where
    assocR (Left (Left a))   = Left a
    assocR (Left (Right b))  = Right (Left b)
    assocR (Right c)         = Right (Right c)
    assocL (Left a)          = Left (Left a)
    assocL (Right (Left b))  = Left (Right b)
    assocL (Right (Right c)) = Right c

plusCommute :: Either a b <-> Either b a
plusCommute = Iso commuteR commuteL
  where
    commuteR (Left a)  = Right a
    commuteR (Right b) = Left b
    commuteL (Left b)  = Right b
    commuteL (Right a) = Left a

zeroPlus :: Either Zero a <-> a
zeroPlus = Iso zeroPlusL zeroPlusR
  where
    zeroPlusL (Left v)  = absurd v
    zeroPlusL (Right a) = a
    zeroPlusR a         = Right a

plusZero :: Either a Zero <-> a
plusZero = plusCommute >>> zeroPlus

unitOne :: () <-> One
unitOne = Iso unitOneL unitOneR
  where
    unitOneL () = FZ
    unitOneR FZ = ()

onePlusOne :: Sum '[One, One] <-> Two
onePlusOne = un -- XXX

plusR :: (b <-> c) -> (Either a b <-> Either a c)
plusR iso = Iso plusRL plusRR
  where
    plusRL (Left a)  = Left a
    plusRL (Right b) = Right (there iso b)
    plusRR (Left a)  = Left a
    plusRR (Right c) = Right (back iso c)
