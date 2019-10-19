{-# LANGUAGE FlexibleContexts #-}

module MemDiagrams where

import           Diagrams.Backend.PGF
import           Diagrams.Prelude

drawLocation :: Diagram B -> Diagram B -> Diagram B
drawLocation lab val = vsep 0.2 [val <> roundedRect 1 1 0.1, lab]

charDia :: String -> Diagram B
charDia s = text s # fontSizeL 0.5 <> phantom (square 0.5 :: D V2 Double)

soupLabels1 :: Diagram B -> [Diagram B]
soupLabels1 cow =
  [ circle 0.2 # fc blue # lw none
  , charDia "$\\alpha$"
  , cow # sized (dims (1 ^& 1))
  ]

soupLabels2 :: [Diagram B]
soupLabels2 =
  [ charDia "$X$"
  , charDia "$3$"
  , triangle 0.4 # fc green # lw none
  ]

relabelled :: [Diagram B] -> [Diagram B] -> [Diagram B]
relabelled = zipWith (\l' l -> vsep 0.2 [l, arrowV (0 ^& 0.5), l'])

soupValues1 :: [Diagram B]
soupValues1 = map (fontSizeL 0.8 . text . show) [2, 7, 5]

drawSoup :: [Diagram B] -> [Diagram B] -> [P2 Double] -> Diagram B
drawSoup labels values locs =
  zipWith drawLocation labels values # zipWith moveTo locs # mconcat

soupLocs :: [P2 Double]
soupLocs =
  [ origin
  , 3 ^& (-2)
  , 5 ^& 1
  ]

fromRight :: Show a => Either a b -> b
fromRight (Right b) = b
fromRight (Left a)  = error $ "Image file not found: " ++ show a

withImages :: [String] -> ([Diagram B] -> Diagram B) -> IO (Diagram B)
withImages imgNames dia = do
  imgs <- map (image . fromRight) <$> mapM (loadImageEmb . mkImgFile) imgNames
  return $ dia imgs
  where
    mkImgFile nm = "images/" ++ nm ++ ".png"

withImage :: String -> (Diagram B -> Diagram B) -> IO (Diagram B)
withImage imgName dia = withImages [imgName] (dia . head)

soup :: IO (Diagram B)
soup = withImage "cow" $ \cow ->
  drawSoup (soupLabels1 cow) soupValues1 soupLocs

relabelledSoup :: IO (Diagram B)
relabelledSoup = withImage "cow" $ \cow ->
  drawSoup (relabelled soupLabels2 (soupLabels1 cow)) soupValues1 soupLocs
