import           Development.Shake
import           Development.Shake.FilePath

main :: IO ()
main = shake shakeOptions $ do
  want ["SpeciesAsConstructors.pdf"]

  "*.pdf" *> \out -> do
    let lhs = replaceExtension out "lhs"
        bib = replaceExtension out "bib"
    need [lhs,bib]
    system' "rubber" ["-f", "-d",lhs]
