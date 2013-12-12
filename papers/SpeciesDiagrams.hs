{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeSynonymInstances #-}
module SpeciesDiagrams where

import           Data.List                           (intersperse)
import           Data.Tree
import           Diagrams.Backend.Postscript.CmdLine
import           Diagrams.Core.Points
import           Diagrams.Prelude                    hiding (arrow)
import           Diagrams.TwoD.Layout.Tree
import           Graphics.SVGFonts.ReadFont

import           Control.Lens                        ((%~), (&), _head, _last)

colors :: [Colour Double]
colors = [red, orange, green, blue, purple, brown, grey, black]

labR, arrowGap :: Double
labR     = 0.3
arrowGap = 0.2

text' :: Double -> String -> Diagram Postscript R2
text' d s = (stroke $ textSVG' (TextOpts s lin INSIDE_H KERN False d d)) # fc black # lw 0

labT :: Int -> Diagram Postscript R2
labT n = text' 1 (show n) # scale labR <> lab n

lab :: Int -> Diagram Postscript R2
lab n = lab' (colors !! n)

lab' :: (TrailLike b, Transformable b, HasStyle b, V b ~ R2) => Colour Double -> b
lab' c = circle labR
       # fc white
       # lc c
       # lw (labR / 5)

cyc :: [Int] -> Double -> Diagram Postscript R2
cyc labs r = cyc' (map lab labs) r

cyc' :: (Monoid' a, TrailLike a, Transformable a, HasStyle a, HasOrigin a, V a ~ R2) => [a] -> Double -> a
cyc' labs r
  = mconcat
  . zipWith (\l (p,a) -> l # moveTo p <> a) labs
  $ zipWith rotateBy
      [1/4, 1/4 + 1/(fromIntegral n) .. ]
      (map mkLink labs)
 where
  n = length labs
  mkLink _ = ( origin # translateX r
             ,
               ( arc startAngle endAngle
                 # scale r
                 <>
                 eqTriangle 0.1
                 # translateX r
                 # rotate endAngle
                 # fc black
               )
               # lw (labR / 10)
             )
  startAngle = Rad $ (labR + arrowGap)/r
  endAngle   = Rad (tau/(fromIntegral n)) - startAngle

newtype Cyc a = Cyc {getCyc :: [a]}
  deriving Functor

data Pointed a = Plain a | Pointed a

class Drawable d where
  draw :: d -> Diagram Postscript R2

instance Drawable (Diagram Postscript R2) where
  draw = id

instance Drawable a => Drawable (Cyc a) where
  draw (Cyc ls) = cyc' (map draw ls # sized (Width (labR*2))) 1

instance Drawable a => Drawable [a] where
  draw ls = centerX . hcat' (with & sep .~ 0.1)
          $ intersperse (arrow 0.5 mempty) (map draw ls)

instance Drawable a => Drawable (Pointed a) where
  draw (Plain a) = draw a
  draw (Pointed a) = point (draw a)

point :: Diagram Postscript R2 -> Diagram Postscript R2
point d = d <> drawSpN Hole # sizedAs (d # scale 5)

down :: Cyc (Diagram Postscript R2) -> Cyc (Cyc (Pointed (Diagram Postscript R2)))

down (Cyc ls) = Cyc (map Cyc (pointings ls))

pointings :: [a] -> [[Pointed a]]
pointings []     = []
pointings (x:xs) = (Pointed x : map Plain xs) : map (Plain x :) (pointings xs)

elimArrow :: Diagram Postscript R2
elimArrow = (hrule 2 # lw 0.03)
        ||| eqTriangle 0.2 # rotateBy (-1/4) # fc black

arrow len l =
  ( l
    ===
    hrule len # lw 0.03
  )
  # alignB
  |||
  eqTriangle 0.2 # rotateBy (-1/4) # fc black

x |-| y = x ||| strutX 1 ||| y

data SpN = Lab (Either Int String) | Leaf | Hole | Point | Sp (Diagram Postscript R2) CircleFrac | Bag

type SpT = Tree SpN

drawSpT' :: T2 -> SymmLayoutOpts SpN -> Tree SpN -> Diagram Postscript R2
drawSpT' tr slopts
  = transform tr
  . renderTree' (drawSpN' (inv tr)) drawSpE
  . symmLayout' slopts

drawSpT :: Tree SpN -> Diagram Postscript R2
drawSpT = drawSpT' (rotation (1/4 :: CircleFrac))
                   (with { slHSep = 0.5, slVSep = 2})

drawSpN' :: Transformation R2 -> SpN -> Diagram Postscript R2
drawSpN' _  (Lab (Left n))  = lab n # scale 0.5
drawSpN' tr (Lab (Right t)) = (drawSpN' tr Leaf ||| strutX (labR/2) ||| text' 0.3 t) # transform tr
drawSpN' _  Leaf     = circle (labR/2) # fc black
drawSpN' _  Hole     = circle (labR/2) # lw (labR / 10) # fc white
drawSpN' tr Point    = drawSpN' tr Leaf <> drawSpN' tr Hole # scale 1.7
drawSpN' tr (Sp s f) = ( arc (3/4 - f/2) (3/4 + f/2) # scale 0.3
                       |||
                       strutX 0.1
                       |||
                       s # transform tr
                       )
drawSpN' _  Bag     =
                ( text' 1 "{" # scale 0.5 ||| strutX (labR/4)
                  ||| circle (labR/2) # fc black
                  ||| strutX (labR/4) ||| text' 1 "}" # scale 0.5
                ) # centerX

drawSpN :: SpN -> Diagram Postscript R2
drawSpN = drawSpN' mempty

drawSpE :: (TrailLike b, HasStyle b) => (t, Point (V b)) -> (SpN, Point (V b)) -> b
drawSpE (_,p) (Hole,q) = (p ~~ q) # dashing [0.05,0.05] 0
drawSpE (_,p) (_,q)    = p ~~ q

nd :: Diagram Postscript R2 -> Forest SpN -> Tree SpN
nd x = Node (Sp x (1/2))

lf :: a -> Tree a
lf x = Node x []

main :: IO ()
main = -- defaultMain (arrow 1 ((text' 1 "f" <> strutY 1) # scale 0.5))

 defaultMain (draw (down (Cyc [lab 0, lab 1, lab 2])))

-- defaultMain (draw (Cyc [Cyc [lab 0, lab 4], Cyc [lab 1, lab 2, lab 3]]))
-- (cyc' (replicate 5 (square 0.2 :: Diagram Postscript R2)) 1)

-- defaultMain (drawSpT (nd 'F' [lf Leaf, lf Hole, Node Bag (map lf [Leaf, Leaf, Hole, Leaf])]))

struct :: Int -> String -> Diagram Postscript R2
struct n x = drawSpT (struct' n x)
           # centerXY

struct' :: Int -> String -> Tree SpN
struct' n x = struct'' n (text' 1 x <> rect 2 1 # lw 0)

struct'' :: Int -> Diagram Postscript R2 -> Tree SpN
struct'' n d = nd d (replicate n (lf Leaf))

linOrd :: [Int] -> Diagram Postscript R2
linOrd ls =
    connect
  . hcat' (with & sep .~ 0.5)
  $ map labT ls & _head %~ named "head" & _last %~ named "last"
  where
    connect =
      withNames ["head", "last"] $ \[h,l] ->
        beneath (location h ~~ location l)

unord :: (Monoid' b, Semigroup b, TrailLike b, Alignable b, Transformable b, HasStyle b, Juxtaposable b, HasOrigin b, Enveloped b, V b ~ R2) => [b] -> b
unord [] = circle 1 # lw 0.1 # lc gray
unord ds = elts # centerXY
           <> roundedRect w (mh + s*2) ((mh + s*2) / 5)
  where
    elts  = hcat' (with & sep .~ s) ds
    mw    = maximum' 0 . map width  $ ds
    s     = mw * 0.5
    mh    = maximum' 0 . map height $ ds
    w     = ((fromIntegral (length ds + 1) * s) +) . sum . map width $ ds
    maximum' d [] = d
    maximum' _ xs = maximum xs

enRect :: (Semigroup a, TrailLike a, Alignable a, Enveloped a, HasOrigin a, V a ~ R2) => a -> a
enRect d = roundedRect (w+0.5) (h+0.5) 0.5 <> d # centerXY
  where (w,h) = size2D d
