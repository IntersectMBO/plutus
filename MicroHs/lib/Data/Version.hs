module Data.Version(
  Version(..),
  showVersion,
  makeVersion
  ) where
import Control.DeepSeq.Class
import Data.List (intercalate)
import MiniPrelude
import Prelude qualified ()

data Version = Version { versionBranch :: [Int] }
  deriving (Show, Eq, Ord)

instance NFData Version where
  rnf (Version x) = rnf x

showVersion :: Version -> String
showVersion (Version b) = intercalate "." (map show b)

{-
parseVersion :: ReadP Version
parseVersion = do branch <- sepBy1 (fmap read (munch1 isDigit)) (char '.')
                  pure Version{versionBranch=branch}
-}
makeVersion :: [Int] -> Version
makeVersion b = Version b
