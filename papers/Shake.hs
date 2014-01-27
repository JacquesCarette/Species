import           Development.Shake
import           Development.Shake.FilePath

lhs2TeX  = "lhs2TeX"
pdflatex = "pdflatex"
bibtex   = "bibtex"

main :: IO ()
main = shake shakeOptions $ do
  want ["LabelledArrays.pdf"]

  "*.tex" *> \output -> do
      let input = output -<.> "lhs"
      need [input, "SpeciesDiagrams.hs"]
      system' lhs2TeX $ ["-o", output] ++ [input]

  "*.pdf" *> \output -> do
      let input = output -<.> "tex"
      need [input, output -<.> "bib"]
      system' pdflatex $ ["--enable-write18", input]
      system' bibtex $ [dropExtension input]
      system' pdflatex $ ["--enable-write18", input]
