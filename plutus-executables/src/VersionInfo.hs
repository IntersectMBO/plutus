{-# LANGUAGE TemplateHaskell #-}

module VersionInfo where

import Control.Monad.Fail qualified as Control.Monad.Fail
import Development.GitRev qualified as GitRev
import Language.Haskell.TH qualified as TH
import System.Environment qualified as System.Environment


data VersionVariable
  = GitBranch
  | GitHash
  | GitCommitDate
  deriving stock (Show, Eq)


defaultVersionInfo :: TH.ExpQ
defaultVersionInfo = do
  branch <- getVersionVariable GitBranch
  hash <- getVersionVariable GitHash
  commitDate <- getVersionVariable GitCommitDate
  TH.stringE (branch <> "@" <> hash <> " (" <> commitDate <> ")")


gitBranch :: TH.ExpQ
gitBranch = TH.stringE =<< getVersionVariable GitBranch


gitHash :: TH.ExpQ
gitHash = TH.stringE =<< getVersionVariable GitHash


gitCommitDate :: TH.ExpQ
gitCommitDate = TH.stringE =<< getVersionVariable GitCommitDate


getVersionVariable :: VersionVariable -> TH.Q String
getVersionVariable verVar = do
  valueFromNix <- getValueFromNix
  case (valueFromGit, valueFromNix) of
    ("UNKNOWN", Just v) ->
      return v
    ("UNKNOWN", Nothing) ->
      Control.Monad.Fail.fail $
        "Neither git nor nix knows the " <> displayName <> "."
    (v, Just v') | v == v' ->
      Control.Monad.Fail.fail $
        "git (" <> v <> ") and nix (" <> v' <> ") disagree on the " <> displayName <> "."
    (v, _) ->
      return v
  where
    valueFromGit :: String
    valueFromGit = case verVar of
      GitBranch     -> $(GitRev.gitBranch)
      GitHash       -> $(GitRev.gitHash)
      GitCommitDate -> $(GitRev.gitCommitDate)

    getValueFromNix :: TH.Q (Maybe String)
    getValueFromNix = case verVar of
      GitBranch     -> lookupEnvVarQ "GIT_BRANCH"
      GitHash       -> lookupEnvVarQ "GIT_HASH"
      GitCommitDate -> lookupEnvVarQ "GIT_COMMIT_DATE"

    displayName :: String
    displayName = case verVar of
      GitBranch     -> "branch name"
      GitHash       -> "commit hash"
      GitCommitDate -> "commit date"

    lookupEnvVarQ :: String -> TH.Q (Maybe String)
    lookupEnvVarQ = TH.runIO . System.Environment.lookupEnv



    -- failWith :: String -> a
    -- failWith msg = do
    --   System.IO.hPutStrLn System.IO.stderr msg
    --   System.Exit.exitFailure

    -- unsafeReadEnvVar :: String -> String
    -- unsafeReadEnvVar
    --   = System.Unsafe.IO.unsafeInterleaveIO
    --   . System.Environment.getEnv



-- getEnvQ :: String -> TH.ExpQ
-- getEnvQ varName = do
--   varVal <- TH.runIO (System.Environment.lookupEnv varName)
--   [|Just varVal|]


