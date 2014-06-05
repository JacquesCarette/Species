import           Development.Shake
import           Development.Shake.FilePath

main :: IO ()
main = shake shakeOptions $ do
  want ["POPL15.pdf"]

  -- "*.tex" *> \output -> do
  --     let input = output -<.> "lhs"
  --     need [input, "SpeciesDiagrams.hs"]
  --     cmd "lhs2TeX --poly -o" [output] [input]

  "*.pdf" *> \output -> do
      let input = output -<.> "tex"
      need [input, output -<.> "bib"]
      () <- cmd "pdflatex --enable-write18" [input]
      () <- cmd "bibtex" [dropExtension input]
      cmd "pdflatex --enable-write18" [input]
