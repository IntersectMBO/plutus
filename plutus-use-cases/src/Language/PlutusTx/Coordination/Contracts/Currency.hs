{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE MonoLocalBinds     #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeOperators      #-}
{-# LANGUAGE ViewPatterns       #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
-- | Implements a custom currency with a monetary policy that allows
--   the forging of a fixed amount of units.
module Language.PlutusTx.Coordination.Contracts.Currency(
      Currency(..)
    , CurrencySchema
    , CurrencyError(..)
    , AsCurrencyError(..)
    , curPolicy
    -- * Actions etc
    , forgeContract
    , forgedValue
    , currencySymbol
    -- * Simple monetary policy currency
    , SimpleMPS(..)
    , forgeCurrency
    ) where

import           Control.Lens
import           Language.PlutusTx.Coordination.Contracts.PubKey (AsPubKeyError (..), PubKeyError)
import qualified Language.PlutusTx.Coordination.Contracts.PubKey as PK
import           Language.PlutusTx.Prelude                       hiding (Monoid (..), Semigroup (..))

import           Language.Plutus.Contract                        as Contract

import qualified Language.PlutusTx                               as PlutusTx
import qualified Language.PlutusTx.AssocMap                      as AssocMap
import           Ledger                                          (CurrencySymbol, PubKeyHash, TxId, TxOutRef (..),
                                                                  pubKeyHash, scriptCurrencySymbol, txId)
import qualified Ledger.Ada                                      as Ada
import qualified Ledger.Constraints                              as Constraints
import qualified Ledger.Contexts                                 as V
import           Ledger.Scripts
import qualified Ledger.Typed.Scripts                            as Scripts
import           Ledger.Value                                    (TokenName, Value)
import qualified Ledger.Value                                    as Value

import           Data.Aeson                                      (FromJSON, ToJSON)
import qualified Data.Map                                        as Map
import           GHC.Generics                                    (Generic)
import           IOTS                                            (IotsType)
import           Prelude                                         (Semigroup (..))
import qualified Prelude
import           Schema                                          (ToSchema)

{-# ANN module ("HLint: ignore Use uncurry" :: String) #-}

data Currency = Currency
  { curRefTransactionOutput :: (TxId, Integer)
  -- ^ Transaction input that must be spent when
  --   the currency is forged.
  , curAmounts              :: AssocMap.Map TokenName Integer
  -- ^ How many units of each 'TokenName' are to
  --   be forged.
  }

PlutusTx.makeLift ''Currency

currencyValue :: CurrencySymbol -> Currency -> Value
currencyValue s Currency{curAmounts = amts} =
    let
        values = map (\(tn, i) -> (Value.singleton s tn i)) (AssocMap.toList amts)
    in fold values

mkCurrency :: TxOutRef -> [(TokenName, Integer)] -> Currency
mkCurrency (TxOutRef h i) amts =
    Currency
        { curRefTransactionOutput = (h, i)
        , curAmounts              = AssocMap.fromList amts
        }

validate :: Currency -> V.PolicyCtx -> Bool
validate c@(Currency (refHash, refIdx) _) ctx@V.PolicyCtx{V.policyCtxTxInfo=txinfo} =
    let
        -- see note [Obtaining the currency symbol]
        ownSymbol = V.ownCurrencySymbol ctx

        forged = V.txInfoForge txinfo
        expected = currencyValue ownSymbol c

        -- True if the pending transaction forges the amount of
        -- currency that we expect
        forgeOK =
            let v = expected == forged
            in traceIfFalse "Value forged different from expected" v

        -- True if the pending transaction spends the output
        -- identified by @(refHash, refIdx)@
        txOutputSpent =
            let v = V.spendsOutput txinfo refHash refIdx
            in  traceIfFalse "Pending transaction does not spend the designated transaction output" v

    in forgeOK && txOutputSpent

curPolicy :: Currency -> MonetaryPolicy
curPolicy cur = mkMonetaryPolicyScript $
    $$(PlutusTx.compile [|| \c -> Scripts.wrapMonetaryPolicy (validate c) ||])
        `PlutusTx.applyCode`
            PlutusTx.liftCode cur

{- note [Obtaining the currency symbol]

The currency symbol is the address (hash) of the validator. That is why
we can use 'Ledger.scriptAddress' here to get the symbol  in off-chain code,
for example in 'forgedValue'.

Inside the validator script (on-chain) we can't use 'Ledger.scriptAddress',
because at that point we don't know the hash of the script yet. That
is why we use 'V.ownCurrencySymbol', which obtains the hash from the
'PolicyCtx' value.

-}

-- | The 'Value' forged by the 'curPolicy' contract
forgedValue :: Currency -> Value
forgedValue cur = currencyValue (currencySymbol cur) cur

currencySymbol :: Currency -> CurrencySymbol
currencySymbol = scriptCurrencySymbol . curPolicy

data CurrencyError =
    CurPubKeyError PubKeyError
    | CurContractError ContractError
    deriving stock (Prelude.Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

makeClassyPrisms ''CurrencyError

instance AsContractError CurrencyError where
    _ContractError = _CurContractError

instance AsPubKeyError CurrencyError where
    _PubKeyError = _CurPubKeyError

-- | @forge [(n1, c1), ..., (n_k, c_k)]@ creates a new currency with
--   @k@ token names, forging @c_i@ units of each token @n_i@.
--   If @k == 0@ then no value is forged. A one-shot monetary policy
--   script is used to ensure that no more units of the currency can
--   be forged afterwards.
forgeContract
    :: forall s e.
    ( HasWriteTx s
    , HasTxConfirmation s
    , AsCurrencyError e
    )
    => PubKeyHash
    -> [(TokenName, Integer)]
    -> Contract s e Currency
forgeContract pk amounts = mapError (review _CurrencyError) $ do
    (txOutRef, txOutTx, pkInst) <- PK.pubKeyContract pk (Ada.lovelaceValueOf 1)
    let theCurrency = mkCurrency txOutRef amounts
        curVali     = curPolicy theCurrency
        lookups     = Constraints.monetaryPolicy curVali
                        <> Constraints.otherScript (Scripts.validatorScript pkInst)
                        <> Constraints.unspentOutputs (Map.singleton txOutRef txOutTx)
    let forgeTx = Constraints.mustSpendScriptOutput txOutRef unitRedeemer
                    <> Constraints.mustForgeValue (forgedValue theCurrency)
    tx <- submitTxConstraintsWith @Scripts.Any lookups forgeTx
    _ <- awaitTxConfirmed (txId tx)
    pure theCurrency

-- | Monetary policy for a currency that has a fixed amount of tokens issued
--   in one transaction
data SimpleMPS =
    SimpleMPS
        { tokenName :: TokenName
        , amount    :: Integer
        }
        deriving stock (Prelude.Eq, Prelude.Show, Generic)
        deriving anyclass (FromJSON, ToJSON, IotsType, ToSchema)

type CurrencySchema =
    BlockchainActions
        .\/ Endpoint "Create native token" SimpleMPS

-- | Use 'forgeContract' to create the currency specified by a 'SimpleMPS'
forgeCurrency
    :: Contract CurrencySchema CurrencyError Currency
forgeCurrency = do
    SimpleMPS{tokenName, amount} <- endpoint @"Create native token"
    ownPK <- pubKeyHash <$> ownPubKey
    forgeContract ownPK [(tokenName, amount)]
