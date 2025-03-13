{-# LANGUAGE TemplateHaskell #-}

module VersionInfo
  ( makeVersionInfo
  ) where


import Data.Version qualified as Data.Version
import GitRevExtra qualified as GitRevExtra
import Language.Haskell.TH qualified as TH
import Paths_plutus_executables qualified as Paths_plutus_executables


makeVersionInfo :: String -> TH.ExpQ
makeVersionInfo execName = do
  let version = Data.Version.showVersion Paths_plutus_executables.version
  [| execName
      <> " version "
      <> version
      <> " - git rev "
      <> $(GitRevExtra.gitHash)
      <> " - "
      <> $(GitRevExtra.gitCommitDate)
    |]
