{-# LANGUAGE TemplateHaskell #-}

module VersionInfoTH
  ( lookupEnvVarAtBuildTime
  ) where


import Language.Haskell.TH qualified as TH
import System.Environment qualified as System.Environment


lookupEnvVarAtBuildTime :: String -> TH.ExpQ
lookupEnvVarAtBuildTime varName = do
  varVal <- TH.runIO (System.Environment.lookupEnv varName)
  [|Just varVal|]
