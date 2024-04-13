module PlutusTx.Utils where

-- We do not use qualified import because the whole module contains off-chain code
import Prelude as Haskell

mustBeReplaced :: String -> a
mustBeReplaced placeholder =
  error $
    "The " <> show placeholder <> " placeholder must have been replaced by the \
      \core-to-plc plugin during compilation."
