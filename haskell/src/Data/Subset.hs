{-# LANGUAGE Rank2Types    #-}
{-# LANGUAGE TypeOperators #-}

module Data.Subset
    (
      -- * Partial isomorphism

      type (<-?>), type (⊆), asPIso, subsetMaybe, subsetLeft, subsetRight, splitProd

    )
    where

import Control.Lens
import Data.Finite
import Data.Vec

-- | The type @a \<-?\> b@ represents /partial isomorphisms/ between
--   @a@ and @b@.  In particular, every value of type @b@ has a
--   corresponding value of type @a@, but the converse is not
--   necessarily true: some values of @a@ may have no corresponding
--   @b@ value.  Intuitively, @a \<-?\> b@ may be thought of as
--   providing computational evidence witnessing the fact that "@a@ is
--   a superset of @b@".
--
--   * To construct one, use @prism' :: (b -\> a) -\> (a -\> Maybe b)
--     -\> (a \<-?\> b)@, being careful to satisfy the laws: for @prism'
--     f g@ we should have (1) @g . f === Just@, and (2) if @g a = Just
--     b@ then @f b = a@.
--
--   * Any isomorphism may be used directly as a partial isomorphism.
--
--   * To turn a partial isomorphism into a function in the forward
--     (partial) direction, use 'preview'.
--
--   * To turn a partial isomorphism into a function in the backwards
--     (total) direction, use 'review'.
--
--   * Unlike with isomorphisms, it does not make sense to invert
--     partial isomorphisms, since they have an inherent directionality.
--
--   * To compose two partial isomorphisms (or an isomorphism and a
--     partial isomorphism), use the normal function composition
--     operator '.' (though note it works \"backwards\", /i.e./ @(.)
--     :: (a \<-?\> b) -> (b \<-?\> c) -> (a \<-?\> c)@.
type (<-?>) a b = Prism' a b

-- | A type to represent (computationally relevant) proofs that one
--   type is a subset of another.  Note that @a ⊆ b@ is equivalent to
--   a partial isomorphism @b <-?> a@ from @b@ to @a@, with the
--   distinction that it may be more easily stored in data structures
--   (avoiding the need for @ImpredicativeTypes@).  To convert to a
--   partial isomorphism, use 'asPIso'.
type (⊆) a b = APrism' b a

-- | Convert a subset proof into a partial isomorphism.
asPIso :: (a ⊆ b) -> (b <-?> a)
asPIso = clonePrism

subsetMaybe :: l ⊆ Maybe l
subsetMaybe = _Just

subsetLeft :: l1 ⊆ Either l1 l2
subsetLeft = _Left

subsetRight :: l2 ⊆ Either l1 l2
subsetRight = _Right

------------------------------------------------------------

splitProd :: Eq l1 => Finite l1 -> Vec (Size l1) (l2 ⊆ (l1,l2))
splitProd fin1 = fmap (fstIs) (enumerate fin1)

fstIs :: Eq a => a -> Prism' (a,b) b
fstIs a = prism' ((,) a) (\(a',b) -> if a == a' then Just b else Nothing)
