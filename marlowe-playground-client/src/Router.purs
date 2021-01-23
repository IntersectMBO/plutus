module Router where

import Prelude hiding ((/))
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe)
import Data.Newtype (unwrap)
import Data.Profunctor (dimap)
import Data.Symbol (SProxy(..))
import Gist (GistId(..))
import Routing.Duplex (RouteDuplex', optional, param, record, root, (:=))
import Routing.Duplex.Generic (noArgs, sum)
import Routing.Duplex.Generic.Syntax ((/))

type Route
  = { subroute :: SubRoute
    , gistId :: Maybe GistId
    }

data SubRoute
  = Home
  | Simulation
  | MarloweEditor
  | HaskellEditor
  | JSEditor
  | ActusBlocklyEditor
  | Blockly
  | Wallets
  | GithubAuthCallback

derive instance eqRoute :: Eq SubRoute

derive instance genericRoute :: Generic SubRoute _

route :: RouteDuplex' Route
route =
  root $ record
    # _gistId
    := optional (dimap unwrap GistId (param "gistid"))
    # _subroute
    := sum
        { "Home": noArgs
        , "Simulation": "simulation" / noArgs
        , "MarloweEditor": "marlowe" / noArgs
        , "HaskellEditor": "haskell" / noArgs
        , "JSEditor": "javascript" / noArgs
        , "Blockly": "blockly" / noArgs
        , "ActusBlocklyEditor": "actus" / noArgs
        , "Wallets": "wallets" / noArgs
        , "GithubAuthCallback": "gh-oauth-cb" / noArgs
        }
  where
  _gistId = SProxy :: SProxy "gistId"

  _subroute = SProxy :: SProxy "subroute"
