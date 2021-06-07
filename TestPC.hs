{-# language LambdaCase #-}

import Control.Monad.Trans.Except
import Control.Monad.IO.Class
import System.FilePath
import System.Directory
import Data.Char (isSpace)
import GHC.Platform

data SettingsError
  = SettingsError_MissingData String
  | SettingsError_BadData String

maybeReadFuzzy :: Read a => String -> Maybe a
maybeReadFuzzy str = case reads str of
  [(x, s)] | all isSpace s -> Just x
  _ -> Nothing

main :: IO ()
main = do
  let platformConstantsFile = "/nix/store/gf5j1wg8qf92m13y5qfvpqiy2sakyw5k-ghc-8.10.4/lib/ghc-8.10.4/platformConstants"
      readFileSafe :: FilePath -> IO String
      readFileSafe path = doesFileExist path >>= \case
        True -> readFile path
        False -> error $ "Missing file: " ++ path

  platformConstantsStr <- readFileSafe platformConstantsFile

  platformConstants <- case maybeReadFuzzy platformConstantsStr of
    Just s -> pure s
    Nothing -> error $ "Can't parse " ++ show platformConstantsFile

  print (platformConstants :: PlatformConstants)