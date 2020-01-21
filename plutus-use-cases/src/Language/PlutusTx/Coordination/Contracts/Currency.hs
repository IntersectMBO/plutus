{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
-- | Implements a custom currency with a monetary policy that allows
--   the forging of a fixed amount of units.
module Language.PlutusTx.Coordination.Contracts.Currency(
      Currency(..)
    , curPolicy
    -- * Actions etc
    , forgeContract
    , forgedValue
    , currencySymbol
    ) where

import           Language.PlutusTx.Prelude  hiding (Semigroup(..))
import qualified Language.PlutusTx.Coordination.Contracts.PubKey as PK

import           Language.Plutus.Contract     as Contract

import qualified Ledger.Ada                 as Ada
import qualified Language.PlutusTx          as PlutusTx
import qualified Language.PlutusTx.AssocMap as AssocMap
import qualified Ledger.Validation          as V
import qualified Ledger.Value               as Value
import           Ledger.Scripts
import qualified Ledger.Typed.Scripts       as Scripts
import           Ledger                     (CurrencySymbol, TxId, PubKey, TxOutRef(..), scriptCurrencySymbol, txInRef)
import           Ledger.Value               (TokenName, Value)

import qualified Data.Set   as Set
import           Prelude (Semigroup(..))

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

validate :: Currency -> V.PendingTxMPS -> Bool
validate c@(Currency (refHash, refIdx) _) p =
    let
        -- see note [Obtaining the currency symbol]
        ownSymbol = V.ownCurrencySymbol p

        forged = V.pendingTxForge p
        expected = currencyValue ownSymbol c

        -- True if the pending transaction forges the amount of
        -- currency that we expect
        forgeOK =
            let v = expected == forged
            in traceIfFalseH "Value forged different from expected" v

        -- True if the pending transaction spends the output
        -- identified by @(refHash, refIdx)@
        txOutputSpent =
            let v = V.spendsOutput p refHash refIdx
            in  traceIfFalseH "Pending transaction does not spend the designated transaction output" v

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
'PendingTx' value.

-}

-- | The 'Value' forged by the 'curPolicy' contract
forgedValue :: Currency -> Value
forgedValue cur = currencyValue (currencySymbol cur) cur

currencySymbol :: Currency -> CurrencySymbol
currencySymbol = scriptCurrencySymbol . curPolicy

-- | @forge [(n1, c1), ..., (n_k, c_k)]@ creates a new currency with
--   @k@ token names, forging @c_i@ units of each token @n_i@.
--   If @k == 0@ then no value is forged.
forgeContract
    :: forall s e.
    ( HasWatchAddress s
    , HasWriteTx s
    , AsContractError e)
    => PubKey
    -> [(TokenName, Integer)]
    -> Contract s e Currency
forgeContract pk amounts = do
    refTxIn <- PK.pubKeyContract pk (Ada.lovelaceValueOf 1)
    let theCurrency = mkCurrency (txInRef refTxIn) amounts
        forgedVal   = forgedValue theCurrency
        curVali     = curPolicy theCurrency

    let forgeTx = mustSpendInput refTxIn <> forgeValue forgedVal (Set.singleton curVali)
    _ <- submitTx forgeTx
    pure theCurrency
