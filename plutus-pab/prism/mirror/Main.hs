{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
module Main where

import           Data.Bifunctor                                        (first)
import           Language.PlutusTx.Coordination.Contracts.Prism.Mirror (MirrorSchema, mirror)
import           Plutus.PAB.ContractCLI                                (commandLineApp)
import           Plutus.PAB.Utils                                      (tshow)

main :: IO ()
main =
    commandLineApp
        $ first tshow
        $ mirror @MirrorSchema
