{-# LANGUAGE TemplateHaskell #-}

module VersionInfo where

import Development.GitRev qualified as GitRev
import Language.Haskell.TH qualified as TH
import System.Environment qualified as System.Environment
import System.Exit qualified as System.Exit
import System.IO qualified as System.IO


data VersionVariable
  = GitBranch
  | GitHash
  | GitCommitDate
  deriving (Show, Eq)


getDefaultVersionInfo :: IO String
getDefaultVersionInfo = do
  branch <- getGitBranch
  hash <- getGitHash
  commitDate <- getGitCommitDate
  return $ branch <> "@" <> hash <> " (" <> commitDate <> ")"


getGitBranch :: IO String
getGitBranch = getVersionVariable GitBranch


getGitHash :: IO String
getGitHash = getVersionVariable GitHash


getGitCommitDate :: IO String
getGitCommitDate = getVersionVariable GitCommitDate


getVersionVariable :: VersionVariable -> IO String
getVersionVariable verVar = do
  fromNix <- getFromNix
  case (fromGit, fromNix) of
    ("UNKNOWN", Just x) ->
      return x
    ("UNKNOWN", Nothing) ->
      failWith $ "Neither git nor nix knows the " <> displayName <> "."
    (x, Just x') | x == x' ->
      failWith $ "git (" <> x <> ") and nix (" <> x' <> ") disagree on the " <> displayName <> "."
    (x, _) ->
      return x
  where
    fromGit :: String
    fromGit = case verVar of
      GitBranch     -> $(GitRev.gitBranch)
      GitHash       -> $(GitRev.gitHash)
      GitCommitDate -> $(GitRev.gitCommitDate)

    getFromNix :: IO (Maybe String)
    getFromNix = case verVar of
      GitBranch     -> System.Environment.lookupEnv "GIT_BRANCH"
      GitHash       -> System.Environment.lookupEnv "GIT_HASH"
      GitCommitDate -> System.Environment.lookupEnv "GIT_COMMIT_DATE"

    displayName :: String
    displayName = case verVar of
      GitBranch     -> "branch name"
      GitHash       -> "commit hash"
      GitCommitDate -> "commit date"

    failWith :: String -> IO a
    failWith msg = do
      System.IO.hPutStrLn System.IO.stderr msg
      System.Exit.exitFailure
