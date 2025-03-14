{-# LANGUAGE TemplateHaskell #-}

module Data.Version.Extras
  ( gitAwareVersionInfo
  ) where


import Data.Version qualified as Data.Version
import Development.GitRev.Extras qualified as GitRev
import Language.Haskell.TH qualified as TH


gitAwareVersionInfo
  :: Data.Version.Version -- | The version, usually coming from Paths_<pkg>.version
  -> TH.ExpQ -- | A string that includes, if available, the git hash and the git commit date
gitAwareVersionInfo version = [| version' <> gitHash <> gitCommitDate |]
  where
    version' = Data.Version.showVersion version

    gitCommitDate = do
      let commitDate = $(GitRev.gitCommitDate)
      if null commitDate then "" else " - " <> commitDate

    gitHash = do
      let hash = $(GitRev.gitHash)
      if null hash then "" else " - git rev " <> hash
