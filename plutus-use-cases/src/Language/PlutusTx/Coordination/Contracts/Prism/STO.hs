{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE MonoLocalBinds     #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeOperators      #-}
{-

This module defines an STO that allocates coins to anyone who

* Presents a specific credential token (one that has been issued by a specific
  credential authority with a specific name) and
* Pays 1 Lovelace to a predefined public key address for every coin forged

The supply (number of tokens created) of the STO is unlimited. This is done so
that we do not need a state machine and can participate in the STO with a single
transaction. In a more realistic setting we would also need constraints on the
validity range of the forging transaction.

-}
module Language.PlutusTx.Coordination.Contracts.Prism.STO(
    STOData(..)
    , policy
    , coins
    ) where

import           Data.Aeson                (FromJSON, ToJSON)
import           GHC.Generics              (Generic)
import qualified Language.PlutusTx         as PlutusTx
import           Language.PlutusTx.Prelude
import           Ledger.Ada                (Ada (..), fromValue)
import           Ledger.Crypto             (PubKeyHash)
import           Ledger.Scripts            (MonetaryPolicy, mkMonetaryPolicyScript, monetaryPolicyHash)
import qualified Ledger.Typed.Scripts      as Scripts
import           Ledger.Validation         (PolicyCtx (..))
import qualified Ledger.Validation         as Validation
import           Ledger.Value              (TokenName, Value)
import qualified Ledger.Value              as Value
import qualified Prelude                   as Haskell


data STOData =
    STOData
        { stoIssuer          :: PubKeyHash
        , stoTokenName       :: TokenName
        , stoCredentialToken :: Value
        }
    deriving stock (Generic, Haskell.Eq, Haskell.Show)
    deriving anyclass (ToJSON, FromJSON)

{-# INLINABLE validateSTO #-}
validateSTO :: STOData -> PolicyCtx -> Bool
validateSTO STOData{stoIssuer,stoCredentialToken,stoTokenName} PolicyCtx{policyCtxTxInfo=txInfo,policyCtxPolicy=ownHash} =
    let tokenOK = stoCredentialToken `Value.leq` Validation.valueSpent txInfo
        Lovelace paidToIssuer = fromValue (Validation.valuePaidTo txInfo stoIssuer)
        forgeOK =
            -- Note that this doesn't prevent any tokens with a name other than
            -- 'stoTokenName' from being forged
            Value.valueOf (Validation.txInfoForge txInfo) (Value.mpsSymbol ownHash) stoTokenName == paidToIssuer
    in tokenOK && forgeOK

policy :: STOData -> MonetaryPolicy
policy stoData = mkMonetaryPolicyScript $
    $$(PlutusTx.compile [|| \c -> Scripts.wrapMonetaryPolicy (validateSTO c) ||]) `PlutusTx.applyCode` PlutusTx.liftCode stoData

-- | A 'Value' of a number of coins issued in the STO
coins :: STOData -> Integer -> Value
coins d@STOData{stoTokenName} n =
    let sym = Value.mpsSymbol (monetaryPolicyHash $ policy d)
    in Value.singleton sym stoTokenName n

PlutusTx.makeLift ''STOData
PlutusTx.makeIsData ''STOData
