{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}
-- | Plutus implementation of an account that can be unlocked with a token.
--   Whoever owns the token can spend the outputs locked by the contract.
--   (A suitable token can be created with the 'Language.PlutusTx.Coordination.Contracts.Currency'
--   contract, or with 'newAccount' in this module)
module Language.PlutusTx.Coordination.Contracts.TokenAccount(
  AccountOwner(..)
  , pay
  , redeem
  , redeemTx
  , balance
  , address
  , newAccount
  ) where

import           Control.Lens
import qualified Data.Map                                          as Map
import           Data.Maybe                                        (fromMaybe)

import           Language.Plutus.Contract
import qualified Language.PlutusTx                                 as PlutusTx

import qualified Language.Plutus.Contract.Typed.Tx                 as TypedTx
import           Ledger                                            (Address, PubKey, TxOut)
import qualified Ledger                                            as Ledger
import           Ledger.TxId                                       (TxId)
import           Ledger.Typed.Scripts                              (ScriptType (..))
import qualified Ledger.Typed.Scripts                              as Scripts
import qualified Ledger.Validation                                 as V
import           Ledger.Value                                      (CurrencySymbol, TokenName, Value)
import qualified Ledger.Value                                      as Value

import qualified Language.PlutusTx.Coordination.Contracts.Currency as Currency

newtype AccountOwner = AccountOwner { unAccountOwner :: (CurrencySymbol, TokenName) }
    deriving newtype Eq

data TokenAccount

instance ScriptType TokenAccount where
    type RedeemerType TokenAccount = ()
    type DataType TokenAccount = AccountOwner

{-# INLINEABLE accountToken #-}
accountToken :: AccountOwner -> Value
accountToken (AccountOwner (symbol, name)) = Value.singleton symbol name 1

{-# INLINEABLE validate #-}
validate :: AccountOwner -> () -> V.PendingTx -> Bool
validate owner _ ptx = V.valueSpent ptx `Value.geq` accountToken owner

scriptInstance :: Scripts.ScriptInstance TokenAccount
scriptInstance =
    Scripts.Validator @TokenAccount $$(PlutusTx.compile [|| validate ||]) $$(PlutusTx.compile [|| wrap ||])
    where
    wrap = Scripts.wrapValidator @AccountOwner @()

address :: Address
address = Scripts.scriptAddress scriptInstance

-- | Pay some money to the given token
pay :: (AsContractError e, HasWriteTx s) => AccountOwner -> Value -> Contract s e TxId
pay owner vl =
    let ds = Ledger.DataScript (PlutusTx.toData owner)
    in writeTxSuccess (payToScript vl address ds)

ownsTxOut :: AccountOwner -> TxOut -> Bool
ownsTxOut owner txout =
    Just owner == (Ledger.txOutData txout >>= PlutusTx.fromData . Ledger.getDataScript)

-- | Create a transaction that spends all outputs belonging to the 'AccountOwner'.
redeemTx
    :: ( HasUtxoAt s )
    => AccountOwner
    -> PubKey
    -> Contract s e UnbalancedTx
redeemTx owner pk = do
    utxos <- utxoAt (Scripts.scriptAddress scriptInstance)
    let filterByOwner _ = ownsTxOut owner
        tx = TypedTx.collectFromScriptFilter filterByOwner utxos scriptInstance ()
    -- TODO. Replace 'PubKey' with a more general 'Address' type of output?
    --       Or perhaps add a field 'requiredTokens' to 'UnbalancedTx' and let the
    --       balancing mechanism take care of providing the token.
    pure $ tx & outputs .~ [pubKeyTxOut (accountToken owner) pk]

-- | Empty the account by spending all outputs belonging to the 'AccountOwner'.
redeem
  :: ( AsContractError e
     , HasWriteTx s
     , HasUtxoAt s
     )
  => PubKey 
  -- ^ Where the token should go after the transaction
  -> AccountOwner
  -- ^ Account owner token
  -> Contract s e TxId
redeem pk owner = redeemTx owner pk >>= writeTxSuccess

-- | @balance owners@ returns the value of all unspent outputs that can be unlocked
--   with @accountToken owners@
balance
    :: ( HasUtxoAt s )
    => AccountOwner
    -> Contract s e Value
balance owner = do
    utxos <- utxoAt (Scripts.scriptAddress scriptInstance)
    let inner =
            foldMap (view Ledger.outValue)
            $ filter (ownsTxOut owner)
            $ fmap snd
            $ Map.toList
            $ fromMaybe Map.empty
            $ utxos ^. at (Scripts.scriptAddress scriptInstance)
    pure inner

-- | Create a new token and return its 'AccountOwner' information.
newAccount
    :: ( HasWatchAddress s
       , HasWriteTx s
       , AsContractError e
       )
    => PubKey
    -> Contract s e AccountOwner
newAccount pk = do
    cur <- Currency.forgeContract pk [("token-account", 1)]
    let sym = Ledger.plcCurrencySymbol (Ledger.scriptAddress (Currency.curValidator cur))
    pure $ AccountOwner (sym, "token-account")


PlutusTx.makeLift ''AccountOwner
PlutusTx.makeIsData ''AccountOwner
