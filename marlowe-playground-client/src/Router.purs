module Router where

import Prelude hiding ((/))
import Data.Generic.Rep (class Generic)
import Routing.Duplex (RouteDuplex', root)
import Routing.Duplex.Generic (noArgs, sum)
import Routing.Duplex.Generic.Syntax ((/))

data Route
  = Home
  | Simulation
  | HaskellEditor
  | Blockly
  | Wallets

derive instance eqRoute :: Eq Route

derive instance genericRoute :: Generic Route _

route :: RouteDuplex' Route
route =
  root
    $ sum
        { "Home": noArgs
        , "Simulation": "simulation" / noArgs
        , "HaskellEditor": "haskell" / noArgs
        , "Blockly": "blockly" / noArgs
        , "Wallets": "wallets" / noArgs
        }
