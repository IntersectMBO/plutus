module PlutusTx.Utils where

import           Prelude

mustBeReplaced :: String -> a
mustBeReplaced message = error $ "This must be replaced by the core-to-plc plugin during compilation: " <> message
