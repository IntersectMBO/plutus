module PlutusTx.Utils where

-- We do not use qualified import because the whole module contains off-chain code
import Prelude as Haskell

mustBeReplaced :: String -> a
mustBeReplaced message = error $ "This must be replaced by the core-to-plc plugin during compilation: " <> message
