{-# LANGUAGE TemplateHaskell #-}

module Data.Version.Extras
  ( gitAwareVersionInfo
  ) where


import Data.Version qualified as Data.Version
import Development.GitRev.Extras qualified as GitRev
import Language.Haskell.TH qualified as TH


gitAwareVersionInfo :: String -> Data.Version.Version -> TH.ExpQ
gitAwareVersionInfo execName version = [|
    execName <>
    " version " <>
    Data.Version.showVersion version <>
    " - git rev " <>
    $(GitRev.gitHash) <>
    " - " <>
    $(GitRev.gitCommitDate)
  |]
