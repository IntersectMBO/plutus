{-# LANGUAGE CPP #-}

module Data.Version.Extras
  ( gitAwareVersionInfo
  ) where

import Data.Version qualified as Data.Version

gitAwareVersionInfo
  :: Data.Version.Version
  -- ^ The version, usually coming from the Paths_<pkg> module
  -> String
gitAwareVersionInfo version = version' <> gitRev <> gitCommitDate
  where
    version' :: String
    version' = Data.Version.showVersion version

#ifdef __GIT_REV__
    gitRev :: String
    gitRev = " - git rev " <> __GIT_REV__
#else
    gitRev :: String
    gitRev = ""
#endif

#ifdef __GIT_COMMIT_DATE__
    gitCommitDate :: String
    gitCommitDate = " - " <> __GIT_COMMIT_DATE__
#else
    gitCommitDate :: String
    gitCommitDate = ""
#endif
