{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TypeFamilies       #-}
module MarloweContract(MarloweContract(..), handlers) where

import           Control.Monad.Freer                 (interpret)
import           Data.Aeson                          (FromJSON, ToJSON)
import           Data.Default                        (Default (def))
import           Data.Text.Prettyprint.Doc           (Pretty (..), viaShow)
import           GHC.Generics                        (Generic)
import qualified Language.Marlowe.Client             as Marlowe
import           Language.PureScript.Bridge          (equal, genericShow, mkSumType)
import           Plutus.PAB.Effects.Contract.Builtin (Builtin, BuiltinHandler (contractHandler), HasDefinitions (..),
                                                      SomeBuiltin (..))
import qualified Plutus.PAB.Effects.Contract.Builtin as Builtin
import           Plutus.PAB.Run.PSGenerator          (HasPSTypes (psTypes))
import           Plutus.PAB.Simulator                (SimulatorEffectHandlers)
import qualified Plutus.PAB.Simulator                as Simulator

data MarloweContract =
    MarloweApp -- The main marlowe contract
    | WalletCompanion -- Wallet companion contract
    | MarloweFollower -- Follower contract
    deriving (Eq, Ord, Show, Read, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty MarloweContract where
    pretty = viaShow

instance HasDefinitions MarloweContract where
    getDefinitions = [ MarloweApp
                     , WalletCompanion
                     , MarloweFollower
                     ]
    getSchema = const [] -- TODO: replace with proper schemas using Builtin.endpointsToSchemas (missing some instances currently)
    getContract = \case
        MarloweApp      -> SomeBuiltin Marlowe.marlowePlutusContract
        WalletCompanion -> SomeBuiltin Marlowe.marloweCompanionContract
        MarloweFollower -> SomeBuiltin Marlowe.marloweFollowContract

instance HasPSTypes MarloweContract where
    psTypes p = [ (equal <*> (genericShow <*> mkSumType)) p ]

handlers :: SimulatorEffectHandlers (Builtin MarloweContract)
handlers =
    Simulator.mkSimulatorHandlers def def
    $ interpret (contractHandler Builtin.handleBuiltin)
