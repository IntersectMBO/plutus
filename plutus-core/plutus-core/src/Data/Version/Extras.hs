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
gitAwareVersionInfo execName version = [| version' <> gitHash <> gitCommitDate |]
  where
    version' = Data.Version.showVersion version

    gitCommitDate =
      case $(GitRev.gitCommitDate) of
        ""   -> ""
        date -> " - " <> date

    gitHash =
      case $(GitRev.gitHash) of
        ""     -> ""
        branch -> " - git rev " <> branch
