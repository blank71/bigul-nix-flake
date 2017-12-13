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
  [ "module Everything where",
    "" ]

prefix :: String
prefix = ""

ordering :: [String]
ordering =
  [ "DynamicallyChecked"
  , "HoareLogic"
  ]

exclusion :: [FindClause Bool]
exclusion =
  [ -- liftOp (flip isPrefixOf) directory "./Notes"
    fileName ==? "Everything.agda" ]

main :: IO ()
main = do
  (ps, fs) <- preprocess <$>
                find always
                  (extension ==? ".agda" &&?
                     (not . or <$> sequence exclusion))
                  "."
  let ms = map (concat . (prefix :) . intersperse ".") fs
  writeFile "Everything.agda" (generateEverything ms)

preprocess :: [FilePath] -> ([FilePath], [[String]])
preprocess =
  unzip .
  sortBy (comparing (((toIndex . head) &&& tail) . snd)) .
  map (id &&& (map (takeWhile isAlpha) . tail . splitPath))
  where
    toIndex :: String -> Int
    toIndex = maybe maxBound id . flip findIndex ordering . (==)

generateEverything :: [String] -> String
generateEverything =
  unlines . (everything_header ++) . map ("import " ++)
