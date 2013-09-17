{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}

-- | Another example.

module Data.Species.Rose
    ( -- * Rose tree structures

      Rose(..), isoRose

      -- * Introduction forms

    , rose_, rose, node, fromRose

      -- * Eliminator

    , elimRose, toRose, toRose'

    )
    where

import           Control.Lens       (Iso, from, iso, view)
import           Data.Functor       ((<$>))
import           Data.Tree

import           Data.BFunctor
import           Data.Finite
import           Data.Species.Convert
import           Data.Species.Elim
import           Data.Species.List
import           Data.Species.Shape
import           Data.Species.Types

-- | @Rose@ represents the shape of (finite) rose trees. It is defined
--   directly according to the recurrence @Rose = X * (L o Rose)@.
newtype Rose l = Rose { unRose :: (X * (Comp L Rose)) l }

-- | An isomorphism to mediate unfolding and refolding @Rose@-structures
--   one step.
isoRose :: Iso (Rose l) (Rose l') ((X*(Comp L Rose)) l) ((X*(Comp L Rose)) l')
isoRose = iso unRose Rose

instance BFunctor Rose where
  bmap g = liftIso isoRose isoRose (bmap g)

-- | Introduce a rose tree shape.
rose_ :: Finite l => (X*(Comp L Rose)) l -> Rose l
rose_ = view (from isoRose)

-- | Introduce a list structure.
rose :: Finite l => Sp (X*(Comp L Rose)) l a -> Sp Rose l a
rose = reshape (view (from isoRose))

rose' :: Sp' (X*(Comp L Rose)) a -> Sp' Rose a
rose' sp' = case sp' of SpEx sp -> SpEx (rose sp)

node :: a -> [Sp' Rose a] -> Sp' Rose a
node a ts = rose' $ prod' (x' a) (compJ'' (fromList ts))

-- | Convert a Haskell rose tree to a labelled rose tree structure.
fromRose :: Tree a -> Sp' Rose a
fromRose (Node a ts) = node a (map fromRose ts)

-- | An eliminator for labelled list structures, the equivalent of
--   'foldr'.
elimRose :: (a -> [r] -> r) -> Elim Rose a r
elimRose f =
  mapElimShape (view isoRose) $
    elimProd (elimX (\a -> elimComp (f a <$> elimList [] (:)) (elimRose f)))

toRose :: Finite l => Sp Rose l a -> Tree a
toRose = fromLabelled

toRose' :: Sp' Rose a -> Tree a
toRose' = fromLabelled'

instance Labelled (Tree a) where
  type EltType (Tree a) = a
  type ShapeOf (Tree a) = Rose
  toLabelled            = fromRose
  elimLabelled          = elimRose Node

{-

Unfortunately it seems we have a bug:

>>> let t = Node 3 [Node 4 [], Node 5 []] :: Tree Int
>>> toRose' (fromRose t)
Node {rootLabel = 5, subForest = [Node {rootLabel = 3, subForest = []},Node {rootLabel = 4, subForest = []}]}

This just goes to show that it really does matter *which* isomorphisms
we choose!

-}

{- --- 0

t = Node 1 [Node 2 []] :: Tree Int

fromRose t
  = fromRose (Node 1 [Node 2 []])
  = node 1 (map fromRose [Node 2 []])
  = rose' $ prod' (x' 1) (compJ'' (fromList [fromRose (Node 2 [])]))
  = rose' $ prod' (SpEx (Struct x_ (V.singleton 1))) (compJ'' (fromList [fromRose (Node 2 [])]))
                                                                         ^^^^^^^^^^^^^^^^^^^^1

{ --- 1

fromRose (Node 2 [])
  = node 2 (map fromRose [])
  = node 2 []
  = rose' $ prod' (x' 2) (compJ'' (fromList []))
  = rose' $ prod' (x' 2) (compJ'' (SpEx nil))
  = rose' $ prod' (x' 2) (compJ'' (SpEx (list $ inl one)))
  = rose' $ prod' (x' 2) (compJ'' (SpEx (list $ inl one)))
  = rose' $ prod' (x' 2) (compJ'' (SpEx (reshape (view (from isoL)) $ inl one)))
  = rose' $ prod' (x' 2) (compJ'' (SpEx (reshape (view (from isoL)) $ inl one)))
  = rose' $ prod' (x' 2) (compJ'' (SpEx (over shape (view (from isoL)) $ inl one)))
  = rose' $ prod' (x' 2) (compJ'' (SpEx (over shape L $ inl one)))
  = rose' $ prod' (x' 2) (compJ'' (SpEx (over shape L $ over shape inl_ one)))
  = rose' $ prod' (x' 2) (compJ'' (SpEx (over shape (L . inl_) one)))
  = rose' $ prod' (x' 2) (compJ'' (SpEx (over shape (L . inl_) (Struct one_ VNil))))
  = rose' $ prod' (x' 2) (compJ'' (SpEx (over shape (L . inl_) (Struct one_ VNil))))
  = rose' $ prod' (x' 2) (compJ'' (SpEx (Struct (L . inl_ $ one_) VNil)))
  = rose' $ prod' (x' 2) (compJ'' (SpEx (Struct (L . inl_ $ One id) VNil)))
  = rose' $ prod' (x' 2) (compJ'' (SpEx (Struct (L (Inl (One id))) VNil)))
  = rose' $ prod' (x' 2) (compJ'' (SpEx (Struct (L (Inl (One id))) VNil)))
                          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^2

{ --- 2

compJ'' (SpEx (Struct (L (Inl (One id))) VNil))
  = case unzipSpSp' VNil of
      UZSS ls gShps gElts ->
        SpEx (Struct
               (Comp (L (Inl (One id))) ls gShps id)
               (V.hconcat Proxy ls gElts)
             )
  = SpEx (Struct (Comp (L (Inl (One id))) LNil HNil id) (V.hconcat Proxy LNil HNil))
  = SpEx (Struct (Comp (L (Inl (One id))) LNil HNil id) VNil)

} --- 1

  = rose' $ prod' (x' 2) (SpEx (Struct (Comp (L (Inl (One id))) LNil HNil id) VNil))
  = rose' $ prod' (SpEx (Struct (X id) (V.singleton 2)))
                  (SpEx (Struct (Comp (L (Inl (One id))) LNil HNil id) VNil))
  = rose' $ SpEx (Struct (Prod (X id) (Comp (L (Inl (One id))) LNil HNil id) id)
                         (V.append (V.singleton 2) VNil))
  = SpEx (Struct (Rose (Prod (X id) (Comp (L (Inl (One id))) LNil HNil id) id))
                 (VCons 2 VNil))

} --- 0

OK, I can see how this is going to end up.  There will be an even more
complicated shape, with more occurrences of Rose and L and X etc.  The
call to prod' is going to append (V.singleton 1) onto (VCons 2 VNil)
so we end up with 1 ::: 2 ::: VNil as observed.

From ghci, using :force:

>>> let sp' = fromRose (Node 1 [Node 2 []] :: Tree Int)
Loading package type-equality-0.1.2 ... linking ... done.
>>> :force sp'
sp' = SpEx
1       (Struct
2          (Rose (Prod
3                   (X _)
4                   (Comp
5                      (L (Inr (Prod (X _) (L (Inl (One _))) _)))
6                      (Data.Type.List.LCons Data.Proxy.Proxy Data.Type.List.LNil)
7                      (Data.Vec.HCons
8                         (Prod
9                            (X _) (Comp (Inl (One _)) Data.Type.List.LNil Data.Vec.HNil _) _)
10                        Data.Vec.HNil)
11                     _)
12                  _))
13         (Data.Vec.VCons 1 (Data.Vec.VCons 2 Data.Vec.VNil)))


-}

{- Then calling toRose' on that produced value above yields:

toRose' (SpEx ...)
  = fromLabelled' (SpEx ...)
  = elim' elimLabelled (SpEx ...)
  = elim' (elimRose Node) (SpEx ...)
  = elim (elimRose Node) ...
  = elim (mapElimShape (view isoRose) $
            elimProd (elimX (\a -> elimComp (Node a <$> elimList [] (:)) (elimRose f)))) ...
  = elim (mapElimShape unRose $
            elimProd (elimX (\a -> elimComp (Node a <$> elimList [] (:)) (elimRose f)))) ...
                     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^3

{ --- 3

elimX (\a -> elimComp (Node a <$> elimList [] (:)) (elimRose f))
  = Elim (\(X i) m -> (\a -> elimComp (Node a <$> elimList [] (:)) (elimRose f)) (m (view i FZ)))
  = Elim (\(X i) m -> elimComp (Node (m (view i FZ)) <$> elimList [] (:)) (elimRose f))

} --- 0

  = elim (mapElimShape unRose $
            elimProd
              (Elim (\(X i) m -> elimComp (Node (m (view i FZ)) <$> elimList [] (:)) (elimRose f))))
         ...
  = elim (mapElimShape unRose $
      Elim $ \(Prod fShp gShp pf) m ->
        let mEither  = m . view pf
            (mf, mg) = (mEither . Left, mEither . Right)
        in
          case (\(X i) m -> elimComp (Node (m (view i FZ)) <$> elimList [] (:)) (elimRose f)) fShp mf of
            Elim g -> g gShp mg) ...

  = elim (mapElimShape unRose $
      Elim $ \(Prod fShp gShp pf) m ->
          case (\(X i) -> elimComp (Node ((m . view pf . Left) (view i FZ)) <$> elimList [] (:)) (elimRose f)) fShp of
            Elim g -> g gShp (m . view pf . Right)
      ) ...

  = elim (Elim $ \s m1 ->
           ( \(Prod fShp gShp pf) m ->
               case (\(X i) -> elimComp (Node ((m . view pf . Left) (view i FZ)) <$> elimList [] (:)) (elimRose f)) fShp of
                 Elim g -> g gShp (m . view pf . Right)
           )
           (unRose s)
           m1
         )
         ...

  = elim (Elim $ \s m ->
           ( \(Prod fShp gShp pf) ->
               case (\(X i) -> elimComp (Node ((m . view pf . Left) (view i FZ)) <$> elimList [] (:)) (elimRose f)) fShp of
                 Elim g -> g gShp (m . view pf . Right)
           )
           (unRose s)
         )
         ...

  = (\s m ->
           ( \(Prod fShp gShp pf) ->
               case (\(X i) -> elimComp (Node ((m . view pf . Left) (view i FZ)) <$> elimList [] (:)) (elimRose f)) fShp of
                 Elim g -> g gShp (m . view pf . Right)
           )
           (unRose s)
    )
    (Rose (Prod ...))
    (V.index (VCons 1 (VCons 2 VNil)) . view (from finite))

  = ( \(Prod fShp gShp pf) ->
        case (\(X i) -> elimComp (Node ((V.index (VCons 1 (VCons 2 VNil)) . view (from finite) . view pf . Left) (view i FZ)) <$> elimList [] (:)) (elimRose f)) fShp of
          Elim g -> g gShp (V.index (VCons 1 (VCons 2 VNil)) . view (from finite) . view pf . Right)
    )
    (Prod (X id) (Comp ...) id)

  = case (\(X i) -> elimComp (Node ((V.index (VCons 1 (VCons 2 VNil)) . view (from finite) . view id . Left) (view i FZ)) <$> elimList [] (:)) (elimRose f)) (X id) of
      Elim g -> g (Comp ...) (V.index (VCons 1 (VCons 2 VNil)) . view (from finite) . view id . Right)

  = case (\(X i) -> elimComp (Node ((V.index (VCons 1 (VCons 2 VNil)) . view (from finite) . Left) (view i FZ)) <$> elimList [] (:)) (elimRose f)) (X id) of
      Elim g -> g (Comp ...) (V.index (VCons 1 (VCons 2 VNil)) . view (from finite) . Right)

  = case elimComp (Node ((V.index (VCons 1 (VCons 2 VNil)) . view (from finite) . Left) (view id FZ)) <$> elimList [] (:)) (elimRose f) of
      Elim g -> g (Comp ...) (V.index (VCons 1 (VCons 2 VNil)) . view (from finite) . Right)

  = case elimComp (Node ((V.index (VCons 1 (VCons 2 VNil)) . view (from finite) . Left) FZ) <$> elimList [] (:)) (elimRose f) of
      Elim g -> g (Comp ...) (V.index (VCons 1 (VCons 2 VNil)) . view (from finite) . Right)

-}
