-- | This module enables finding data dependencies ("runfiles") of Haskell
-- binaries at runtime.
--
-- For more information, see: https://github.com/bazelbuild/bazel/issues/4460
--
-- Note: this does not currently support the RUNFILES_MANIFEST environmental
-- variable.  However, that's only necessary on Windows, which rules_haskell
-- doesn't support yet.
--
-- Additionally, this is not yet supported by the REPL.
module Bazel.Runfiles
    ( Runfiles
    , create
    , createMaybe
    , rlocation
    , env
    , (</>)
    ) where

import           System.Directory   (doesDirectoryExist)
import           System.Environment (getExecutablePath, lookupEnv)
import           System.FilePath    (FilePath, (<.>), (</>))

-- | A path to a directory tree containing runfiles for the given
newtype Runfiles = Runfiles FilePath
    deriving Show

-- | Construct a path to a data dependency within the given runfiles.
--
-- For example: @rlocation \"myworkspace/mypackage/myfile.txt\"@
rlocation :: Runfiles -> FilePath -> FilePath
rlocation (Runfiles f) g = f </> g

-- | Set environmental variables for locating the given runfiles directory.
--
-- Note that Bazel will set these automatically when it runs tests
-- (@bazel test@).  However, it will not automatically set them
-- during "bazel run"; thus, non-test binaries should set the
-- environment manually for processes that they call.
env :: Runfiles -> [(String, String)]
env (Runfiles f) = [(runfilesDirEnv, f)]

runfilesDirEnv :: String
runfilesDirEnv = "RUNFILES_DIR"

-- | Locate the runfiles directory for the current binary.
--
-- This behaves according to the specification in:
-- https://docs.google.com/document/d/e/2PACX-1vSDIrFnFvEYhKsCMdGdD40wZRBX3m3aZ5HhVj4CtHPmiXKDCxioTUbYsDydjKtFDAzER5eg7OjJWs3V/pub
--
-- Note: it does not currently support the @RUNFILES_MANIFEST@ environmental
-- variable.  However, that's only necessary on Windows, which rules_haskell
-- doesn't support yet anyway.
{-# ANN create "HLint: ignore" #-}
create :: IO Runfiles
create = do
    mr <- createMaybe
    case mr of
      Just r  -> pure r
      Nothing -> error "Unable to locate runfiles directory"

createMaybe :: IO (Maybe Runfiles)
createMaybe = do
    exeRunfilesPath <- fmap (<.> "runfiles") getExecutablePath
    exeRunfilesExists <- doesDirectoryExist exeRunfilesPath
    if exeRunfilesExists
      then return . Just $ Runfiles exeRunfilesPath
      else do
        envDir <- lookupEnv runfilesDirEnv
        case envDir of
            Just f  -> return . Just $ Runfiles f
            Nothing -> return Nothing
