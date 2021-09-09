{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}

module WriteScriptsTo() where

import           Data.Int                      (Int64)
import           Data.Monoid                   (Sum)
import           Ledger                        (ExBudget)
import           Plutus.Trace.Emulator         (EmulatorConfig, EmulatorTrace)
import           Plutus.Trace.Emulator.Extract as Extract

-- BLOCK0
{-| Run an emulator trace and write the applied scripts to a file in Flat format
    using the name as a prefix.
-}
writeScriptsTo
    :: ScriptsConfig -- ^ Configuration
    -> String -- ^ Prefix to be used for file names
    -> EmulatorTrace a -- ^ Emulator trace to extract transactions from
    -> EmulatorConfig -- ^ Emulator config
    -> IO (Sum Int64, ExBudget) -- Total size and 'ExBudget' of extracted scripts
-- BLOCK1
writeScriptsTo = Extract.writeScriptsTo
