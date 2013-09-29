{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

-- | Length-indexed vectors.  Note that this module is designed to be
--   imported qualified.

module Data.Vec
    ( -- * Length-indexed vectors

      Vec(..), fromList, singleton, mkV

    , Vec'(..), vnil', vcons'

      -- ** Operations on length-indexed vectors

    , size, head, tail, index, lookup, append, append', concat, concat'
    , zip, zipWith, unzip, shuffle , permute, fins, enumerate

      -- * Length-indexed, type-indexed heterogeneous vectors

    , HVec(..), toHVec, hProxy, hconcat, VecsOfSize
    )
    where

import           Prelude hiding (concat, unzip, zip, zipWith, lookup, head, tail)

import           Control.Lens    (view,from)
import           Data.Functor    ((<$>))
import           Data.Proxy

import           Data.Fin        (Fin(..))
import qualified Data.Finite     as Finite
import           Data.Iso        (type (<->))
import           Data.Finite     (Finite, Size)
import           Data.Type.List
import           Data.Type.Nat

------------------------------------------------------------
-- Type declarations
------------------------------------------------------------

-- | Standard length-indexed vectors.
data Vec :: Nat -> * -> * where
  VNil :: Vec Z a
  VCons :: a -> Vec n a -> Vec (S n) a

instance Functor (Vec n) where
  fmap _ VNil = VNil
  fmap f (VCons a v) = VCons (f a) (fmap f v)

deriving instance (Show a) => Show (Vec n a)

-- | Length-indexed vectors with an existentially quantified length.
data Vec' :: * -> * where
  SomeVec :: Vec n a -> Vec' a

-- | Convenience constructor for @Vec'@.
vnil' :: Vec' a
vnil' = SomeVec VNil

-- | Convenience constructor for @Vec'@.
vcons' :: a -> Vec' a -> Vec' a
vcons' a (SomeVec v) = SomeVec (VCons a v)

------------------------------------------------------------
-- Operations on Vec
------------------------------------------------------------

-- | Compute the (statically known) size of a vector.
size :: Vec n a -> SNat n
size VNil = SZ
size (VCons _ v) = SS (size v)

-- | Convert a list to a vector with an existentially quantified size.
fromList :: [a] -> Vec' a
fromList []     = vnil'
fromList (a:as) = vcons' a (fromList as)

singleton :: a -> Vec (S Z) a
singleton a = VCons a VNil

head :: Vec (S n) a -> a
head (VCons a _) = a

tail :: Vec (S n) a -> Vec n a
tail (VCons _ v) = v

index :: Vec n a -> Fin n -> a
index (VCons a _) FZ     = a
index (VCons _ v) (FS f) = index v f

lookup :: Eq a => Vec n a -> a -> Maybe (Fin n)
lookup VNil _ = Nothing
lookup (VCons a v) x
  | a == x    = Just FZ
  | otherwise = FS <$> lookup v x

mkV :: SNat n -> (Fin n -> a) -> Vec n a
mkV SZ     _ = VNil
mkV (SS n) f = VCons (f FZ) (mkV n (f . FS))

unzip :: Vec n (a,b) -> (Vec n a, Vec n b)
unzip VNil = (VNil, VNil)
unzip (VCons (a,b) v) = (VCons a va, VCons b vb)
  where (va,vb) = unzip v

zip :: Vec n a -> Vec n b -> Vec n (a,b)
zip = zipWith (,)

zipWith :: (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
zipWith _ VNil VNil = VNil
zipWith f (VCons a as) (VCons b bs) = VCons (f a b) (zipWith f as bs)

-- | Construct a length-@n@ vector containing all the values of @Fin
--   n@, ordered from smallest (@FZ@) to greatest.
fins :: SNat n -> Vec n (Fin n)
fins SZ     = VNil
fins (SS n) = VCons FZ (fmap FS (fins n))

-- | Construct a vector containing the complete list of values of any
--   'Finite' type.
enumerate :: Finite l -> Vec (Size l) l
enumerate p@(Finite.F f) = fmap (view f) (fins (Finite.size p))

append :: Vec k l -> Vec k' l -> Vec (Plus k k') l
append VNil v = v
append (VCons a v) v' = VCons a (append v v')

append' :: Vec' l -> Vec' l -> Vec' l
append' (SomeVec VNil) v         = v
append' (SomeVec (VCons a v)) v' = vcons' a (append' (SomeVec v) v')

-- | Flatten a vector of vectors into a single vector.
concat :: Vec i (Vec j a) -> Vec (Times i j) a
concat VNil = VNil
concat (VCons v vs) = append v (concat vs)

-- | Flatten a vector of vectors of unknown length into a single
--   vector (also of unknown length).  Note that this allows for
--   \"ragged\" vectors, whereas 'concat' does not.
concat' :: Vec k (Vec' a) -> Vec' a
concat' VNil = SomeVec VNil
concat' (VCons v vs) = append' v (concat' vs)

-- | Construct a new vector from old, given a way to map indices of
--   the new vector onto indices of the old.
shuffle :: SNat m -> SNat n -> (Fin n -> Fin m) -> (Vec m a -> Vec n a)
shuffle _ n f v = mkV n (index v . f)

-- | Uses forward direction of an isomorphism to 'shuffle' a set of indicies
-- from a source order to a target order 
permute :: SNat n -> (Fin n <-> Fin n) -> (Vec n a -> Vec n a)
permute n f v = shuffle n n (view (from f)) v

------------------------------------------------------------
-- HVec: Length-indexed, type-indexed heterogeneous vectors
------------------------------------------------------------

-- | A value of type @HVec n ts@ is a length-@n@ vector with element
--   types given by the type-level list @ts@.
data HVec :: Nat -> [*] -> * where
  HNil   :: HVec Z '[]
  HCons  :: l -> HVec n ls -> HVec (S n) (l ': ls)

-- | Convert a @Vec@ to a homogeneous @HVec@.
toHVec :: Vec n a -> HVec n (Replicate n a)
toHVec VNil        = HNil
toHVec (VCons a v) = HCons a (toHVec v)

-- | Discard the data from an @HVec@, resulting in an @LProxy@
--   recording the number and type of its elements.
hProxy :: HVec n ls -> LProxy n ls
hProxy HNil               = LNil
hProxy (HCons (_ :: l) h) = LCons (Proxy :: Proxy l) (hProxy h)

-- | Given a heterogeneous vector of vectors with sizes (n1, n2, ...),
--   concatenate them to give a single vector of size (n1 + n2 + ...).
hconcat :: Proxy g -> LProxy n l2s -> HVec n (VecsOfSize l2s a) -> Vec (Size (Sum l2s)) a
hconcat _ LNil HNil                 = VNil
hconcat p (LCons _ ls) (HCons v vs) = append v (hconcat p ls vs)

-- | Essentially, @VecsOfSize ls a = Map ((\\n -> Vec n a) . Size) ls@,
--   but we can't write that explicitly, because (1) Haskell does not
--   have type-level lambdas, and (2) the type family @Size@ must be
--   fully applied.
--
--   For example, @VecsOfSize '[Bool, ()] Int == '[Vec 2 Int, Vec 1 Int]@.
type family VecsOfSize (ls :: [*]) (a :: *) :: [*]
type instance VecsOfSize '[] a         = '[]
type instance VecsOfSize (l ': ls) a = (Vec (Size l) a ': VecsOfSize ls a)
