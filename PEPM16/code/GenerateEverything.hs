import Data.List hiding (find)
import Data.Char
import Data.Ord
import Data.Maybe
import Control.Arrow
import Control.Monad
import Control.Applicative
import System.IO
import System.FilePath
import System.FilePath.Find


everything_header :: [String]
everything_header =
  [ "module BiGUL.Everything where",
    "" ]

readme_header :: [String]
readme_header =
  [ "# BiGUL: A formally verified core language for putback-based bidirectional programming",
    "",
    "This is the Agda source for the paper with the above title appearing in " ++
    "_Partial Evaluation and Program Manipulation_ 2016 " ++
    "(doi: [10.1145/2847538.2847544](http://dx.doi.org/10.1145/2847538.2847544)).",
    "",
    "All files have been typechecked with Agda version 2.4.2.4 and Standard Library version 0.11.",
    "",
    "A hyperlinked HTML version of the code is under the directory `html`. " ++
    "(All BiGUL modules are listed in `html/BiGUL.Everything.html`.)",
    "",
    "See [the BiGUL project homepage]" ++
    "(http://www.prg.nii.ac.jp/project/bigul/) " ++
    "for more information." ++
    "",
    "## Module descriptions",
    "" ]

prefix :: String
prefix = ""

ordering :: [String]
ordering = [ "BiGUL" ]

exclusion :: [FindClause Bool]
exclusion = [ fileName ==? "Everything.agda" ]

main :: IO ()
main = do
  (ps, fs) <- preprocess <$>
                find always
                  (extension ==? ".agda" &&?
                     (not . or <$> sequence exclusion))
                  "."
  hs <- mapM readHeader ps
  let ms = map (concat . (prefix :) . intersperse ".") fs
  writeFile "BiGUL/Everything.agda" (generateEverything ms)
  writeFile "README.md"             (generateReadme (zip ms hs))

preprocess :: [FilePath] -> ([FilePath], [[String]])
preprocess =
  unzip .
  sortBy (comparing (((toIndex . head) &&& tail) . snd)) .
  map (id &&& (map (takeWhile isAlpha) . tail . splitPath))
  where
    toIndex :: String -> Int
    toIndex = maybe maxBound id . flip findIndex ordering . (==)

readHeader :: FilePath -> IO [String]
readHeader path =
  map (dropWhile isSpace . dropWhile (== '-')) .
  takeWhile ((== "--") . take 2) . lines <$> readFile path

generateEverything :: [String] -> String
generateEverything =
  unlines . (everything_header ++) . map ("import " ++)

generateReadme :: [(String, [String])] -> String
generateReadme =
  unlines . (readme_header ++) . concat . intersperse [""] .
  map (\(m, hs) -> ("#### " ++ m) : hs)

