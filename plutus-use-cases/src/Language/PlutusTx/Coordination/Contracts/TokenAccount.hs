{-# LANGUAGE ConstraintKinds    #-}
{-# LANGUAGE TypeOperators      #-}
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
  -- * Contract functionality
  , pay
  , redeem
  , newAccount
  , balance
  , address
  , accountToken
  -- * Endpoints
  , TokenAccountSchema
  , HasTokenAccountSchema
  , tokenAccountContract
  ) where

import           Control.Lens
import           Control.Monad                                     (void)
import qualified Data.Map                                          as Map
import           Data.Maybe                                        (fromMaybe)

import           Language.Plutus.Contract
import qualified Language.PlutusTx                                 as PlutusTx

import qualified Language.Plutus.Contract.Typed.Tx                 as TypedTx
import           Ledger                                            (Address, PubKey, TxOutTx (..))
import qualified Ledger                                            as Ledger
import           Ledger.TxId                                       (TxId)
import           Ledger.Typed.Scripts                              (ScriptType (..))
import qualified Ledger.Typed.Scripts                              as Scripts
import qualified Ledger.Validation                                 as V
import           Ledger.Value                                      (CurrencySymbol, TokenName, Value)
import qualified Ledger.Value                                      as Value

import qualified Language.PlutusTx.Coordination.Contracts.Currency as Currency

newtype AccountOwner = AccountOwner { unAccountOwner :: (CurrencySymbol, TokenName) }
    deriving newtype (Eq, Show)

data TokenAccount

instance ScriptType TokenAccount where
    type RedeemerType TokenAccount = ()
    type DataType TokenAccount = AccountOwner

type TokenAccountSchema =
    BlockchainActions
        .\/ Endpoint "redeem" (AccountOwner, PubKey)
        .\/ Endpoint "pay" (AccountOwner, Value)
        .\/ Endpoint "new-account" (TokenName, PubKey)

type HasTokenAccountSchema s =
    ( HasBlockchainActions s
    , HasEndpoint "redeem" (AccountOwner, PubKey) s
    , HasEndpoint "pay" (AccountOwner, Value) s
    , HasEndpoint "new-account" (TokenName, PubKey) s
    )

-- | 'transfer', 'redeem', 'pay' and 'newAccount' with endpoints.
tokenAccountContract
    :: forall s e.
       ( HasTokenAccountSchema s
       , AsContractError e
       )
    => Contract s e ()
tokenAccountContract = redeem_ <|> pay_ <|> newAccount_ where
    redeem_ = do
        (accountOwner, destination) <- endpoint @"redeem" @(AccountOwner, PubKey) @s
        void $ redeem destination accountOwner
        tokenAccountContract
    pay_ = do
        (accountOwner, value) <- endpoint @"pay" @_ @s
        void $ pay accountOwner value
        tokenAccountContract
    newAccount_ = do
        (tokenName, initialOwner) <- endpoint @"new-account" @_ @s
        void $ newAccount tokenName initialOwner
        tokenAccountContract

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

-- | Pay some money to the given token account
pay :: (AsContractError e, HasWriteTx s) => AccountOwner -> Value -> Contract s e TxId
pay owner vl =
    let ds = Ledger.DataScript (PlutusTx.toData owner)
    in writeTxSuccess (payToScript vl address ds)

ownsTxOut :: AccountOwner -> TxOutTx -> Bool
ownsTxOut owner (TxOutTx tx txout) =
    let fromDataScript = PlutusTx.fromData @AccountOwner . Ledger.getDataScript in
    Just owner == (Ledger.txOutData txout >>= Ledger.lookupData tx >>= fromDataScript)

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
            foldMap (view Ledger.outValue . Ledger.txOutTxOut)
            $ Map.filter (ownsTxOut owner)
            $ fromMaybe Map.empty
            $ utxos ^. at (Scripts.scriptAddress scriptInstance)
    pure inner

-- | Create a new token and return its 'AccountOwner' information.
newAccount
    :: ( HasWatchAddress s
       , HasWriteTx s
       , AsContractError e
       )
    => TokenName
    -- ^ Name of the token
    -> PubKey
    -- ^ Public key of the token's initial owner
    -> Contract s e AccountOwner
newAccount tokenName pk = do
    cur <- Currency.forgeContract pk [(tokenName, 1)]
    let sym = Ledger.scriptCurrencySymbol (Currency.curValidator cur)
    pure $ AccountOwner (sym, tokenName)

PlutusTx.makeLift ''AccountOwner
PlutusTx.makeIsData ''AccountOwner
