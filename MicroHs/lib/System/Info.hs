module System.Info(os, arch, compilerName, compilerVersion, fullCompilerVersion) where
import Control.Monad
import Data.Char
import Data.Version
import System.Cmd
import System.Directory
import System.Exit
import System.IO
import System.IO.Unsafe

os :: String
os = if _isWindows then "windows" else uname "-s"

arch :: String
arch = if _isWindows then "x86_64" else uname "-m"

compilerName :: String
compilerName = "mhs"

compilerVersion :: Version
compilerVersion = fullCompilerVersion { versionBranch = take 2 (versionBranch fullCompilerVersion) }

-- Assume the system has an uname command
uname :: String -> String
uname flag = unsafePerformIO $ do
  (fn, h) <- openTmpFile "uname"
  hClose h
  rc <- system $ "uname " ++ flag ++ " >" ++ fn
  res <- readFile fn
  removeFile fn
  when (rc /= ExitSuccess) $
    error "System.Into: uname failed"
  return $ map toLower $ filter (not . isSpace) res

fullCompilerVersion = makeVersion [0,13,2,0]
