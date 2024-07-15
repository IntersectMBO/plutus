module Main (main) where

import Options.Applicative qualified as O
import Plutus.Script.Evaluation.Dump (dumpScriptEvents)
import Plutus.Script.Evaluation.Options (parserInfo)

{- Example:

cabal run dump-script-events -- \
  --mainnet \
  --socket-path "$CARDANO_NODE_SOCKET_PATH" \
  --config "$CARDANO_NODE_CONFIG_PATH" \
  --blocks-per-file 50000 \
  --events-per-file 50000 \
  --dump-dir dumps \
  --checkpoint-dir dumps/checkpoints
-}
main :: IO ()
main = dumpScriptEvents =<< O.execParser parserInfo
