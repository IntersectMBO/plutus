{-# LANGUAGE TypeApplications #-}
module Main where

import           Data.Bifunctor                (first)
import           Data.Text.Extras              (tshow)
import           Plutus.Contracts.Prism.Mirror (MirrorSchema, mirror)
import           Plutus.PAB.ContractCLI        (commandLineApp)

main :: IO ()
main =
    commandLineApp
        $ first tshow
        $ mirror @MirrorSchema @()
