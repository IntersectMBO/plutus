{-# LANGUAGE TemplateHaskell #-}

{-
This module provides Template Haskell functions to retrieve git version information
(branch name, commit hash, commit date, and commit count) at compile time.
It attempts to get these values by reading the .git folder.
If the values are not available (e.g., when building outside of a git repository,
or when building with Nix), it falls back to environment variables.

Usage:

@
module MyPrograms where

import Development.GitRev.Extras (gitHash, gitCommitDate)

main :: IO ()
main = do
  -- Falls back to reading the GIT_BRANCH env var
  putStrLn $ "git branch: " <> $(gitBranch)

  -- Falls back to reading the GIT_BRANCH env var
  putStrLn $ "git rev: " <> $(gitHash)

  -- Falls back to reading the GIT_COMMIT_DATE env var
  putStrLn $ "git commit date: " <> $(gitCommitDate)

  -- Falls back to reading the GIT_COMMIT_COUNT env var
  putStrLn $ "git commit count: " <> $(gitCommitCount)
@

When building with haskell.nix, this snippet can be used to inject the env vars:

@
haskellNix.cabalProject' {
  ...
  modules = [{
    packages = {
      <package>.components.exes.<exe>.preBuild = ''
        export GIT_HASH=${inputs.self.sourceInfo.rev or "unknown"}
        export GIT_COMMIT_DATE=${inputs.self.sourceInfo.lastModifiedDate}
      '';
    };
  }];
};
@
-}

module Development.GitRev.Extras
  ( gitBranch
  , gitHash
  , gitCommitDate
  , gitCommitCount
  ) where

import Control.Monad.Fail qualified as Control.Monad.Fail
import Development.GitRev qualified as GitRev
import Language.Haskell.TH qualified as TH
import System.Environment qualified as System.Environment


data VersionVariable
  = GitBranch
  | GitHash
  | GitCommitDate
  | GitCommitCount
  deriving stock (Show, Eq)


-- | Falls back to reading the GIT_BRANCH env var.
gitBranch :: TH.ExpQ
gitBranch = TH.stringE =<< getVersionVariable GitBranch


-- | Falls back to reading the GIT_HASH env var.
gitHash :: TH.ExpQ
gitHash = TH.stringE =<< getVersionVariable GitHash


-- | Falls back to reading the GIT_COMMIT_DATE env var.
gitCommitDate :: TH.ExpQ
gitCommitDate = TH.stringE =<< getVersionVariable GitCommitDate


-- | Falls back to reading the GIT_COMMIT_COUNT env var.
gitCommitCount :: TH.ExpQ
gitCommitCount = TH.stringE =<< getVersionVariable GitCommitCount


getVersionVariable :: VersionVariable -> TH.Q String
getVersionVariable verVar = do
  valueFromEnv <- getValueFromEnv
  case (valueFromGit, valueFromEnv) of
    ("UNKNOWN", Just v) ->
      return v
    ("UNKNOWN", Nothing) ->
      noValueFound
    (v, Just v') | v /= v' ->
      inconsistentValues v v'
    (v, _) ->
      return v
  where
    valueFromGit :: String
    valueFromGit = case verVar of
      GitBranch      -> $(GitRev.gitBranch)
      GitHash        -> $(GitRev.gitHash)
      GitCommitDate  -> $(GitRev.gitCommitDate)
      GitCommitCount -> $(GitRev.gitCommitCount)

    getValueFromEnv :: TH.Q (Maybe String)
    getValueFromEnv = lookupEnvQ envVarName

    envVarName :: String
    envVarName = case verVar of
      GitBranch      -> "GIT_BRANCH"
      GitHash        -> "GIT_HASH"
      GitCommitDate  -> "GIT_COMMIT_DATE"
      GitCommitCount -> "GIT_COMMIT_COUNT"

    displayName :: String
    displayName = case verVar of
      GitBranch      -> "branch name"
      GitHash        -> "commit hash"
      GitCommitDate  -> "commit date"
      GitCommitCount -> "commit count"

    lookupEnvQ :: String -> TH.Q (Maybe String)
    lookupEnvQ = TH.runIO . System.Environment.lookupEnv

    inconsistentValues :: String -> String -> TH.Q String
    inconsistentValues v v' =
      Control.Monad.Fail.fail $
        "Inconsistent values for the "
          <> displayName
          <> ": git reports "
          <> v
          <> " while the env var "
          <> envVarName
          <> " is set to "
          <> v'
          <> "."

    noValueFound :: TH.Q String
    noValueFound =
      Control.Monad.Fail.fail $
        "No value found for the "
          <> displayName
          <> " neither from git nor from the env var "
          <> envVarName
          <> "."
