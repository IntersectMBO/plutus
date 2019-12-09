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
  Account(..)
  -- * Contract functionality
  , pay
  , redeem
  , newAccount
  , balance
  , address
  , accountToken
  , payTx
  -- * Endpoints
  , TokenAccountSchema
  , HasTokenAccountSchema
  , tokenAccountContract
  -- * Etc.
  , TokenAccount
  , assertAccountBalance
  , validatorHash
  , scriptInstance
  ) where

import           Control.Lens
import           Control.Monad                                     (void)
import qualified Data.Map                                          as Map
import           Data.Maybe                                        (fromMaybe)
import           Data.Text.Prettyprint.Doc

import           Language.Plutus.Contract
import qualified Language.PlutusTx                                 as PlutusTx

import qualified Language.Plutus.Contract.Typed.Tx                 as TypedTx
import           Language.Plutus.Contract.Test                     (TracePredicate, fundsAtAddress)
import           Ledger                                            (Address, PubKey, TxOutTx (..), ValidatorHash)
import qualified Ledger                                            as Ledger
import qualified Ledger.Scripts
import           Ledger.TxId                                       (TxId)
import           Ledger.Typed.Scripts                              (ScriptType (..))
import qualified Ledger.Typed.Scripts                              as Scripts
import qualified Ledger.Validation                                 as V
import           Ledger.Value                                      (CurrencySymbol, TokenName, Value)
import qualified Ledger.Value                                      as Value

import qualified Language.PlutusTx.Coordination.Contracts.Currency as Currency

newtype Account = Account { accountOwner :: (CurrencySymbol, TokenName) }
    deriving newtype (Eq, Show)

instance Pretty Account where
    pretty (Account (s, t)) = pretty s <+> pretty t

data TokenAccount

instance ScriptType TokenAccount where
    type RedeemerType TokenAccount = ()
    type DataType TokenAccount = ()

type TokenAccountSchema =
    BlockchainActions
        .\/ Endpoint "redeem" (Account, PubKey)
        .\/ Endpoint "pay" (Account, Value)
        .\/ Endpoint "new-account" (TokenName, PubKey)

type HasTokenAccountSchema s =
    ( HasBlockchainActions s
    , HasEndpoint "redeem" (Account, PubKey) s
    , HasEndpoint "pay" (Account, Value) s
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
        (accountOwner, destination) <- endpoint @"redeem" @(Account, PubKey) @s
        void $ redeem destination accountOwner
        tokenAccountContract
    pay_ = do
        (accountOwner, value) <- endpoint @"pay" @_ @s
        void $ pay (scriptInstance accountOwner) value
        tokenAccountContract
    newAccount_ = do
        (tokenName, initialOwner) <- endpoint @"new-account" @_ @s
        void $ newAccount tokenName initialOwner
        tokenAccountContract

{-# INLINEABLE accountToken #-}
accountToken :: Account -> Value
accountToken (Account (symbol, name)) = Value.singleton symbol name 1

{-# INLINEABLE validate #-}
validate :: Account -> () -> () -> V.PendingTx -> Bool
validate account _ _ ptx = V.valueSpent ptx `Value.geq` accountToken account

scriptInstance :: Account -> Scripts.ScriptInstance TokenAccount
scriptInstance account =
    let wrap = Scripts.wrapValidator @() @()
        val = $$(PlutusTx.compile [|| validate ||])
                `PlutusTx.applyCode`
                    PlutusTx.liftCode account

    in Scripts.validator @TokenAccount
        val
        $$(PlutusTx.compile [|| wrap ||])

address :: Account -> Address
address = Scripts.scriptAddress . scriptInstance

validatorHash :: Account -> ValidatorHash
validatorHash = Ledger.Scripts.validatorHash . Scripts.validatorScript . scriptInstance

-- | A transaction that pays the given value to the account
payTx 
    :: 
    Scripts.ScriptInstance TokenAccount
    -> Value
    -> UnbalancedTx
payTx inst vl = payToScript vl (Scripts.scriptAddress inst) Ledger.Scripts.unitData

-- | Pay some money to the given token account
pay :: (AsContractError e, HasWriteTx s) => Scripts.ScriptInstance TokenAccount -> Value -> Contract s e TxId
pay inst = submitTx . payTx inst

-- | Create a transaction that spends all outputs belonging to the 'Account'.
redeemTx
    :: ( HasUtxoAt s )
    => Account
    -> PubKey
    -> Contract s e UnbalancedTx
redeemTx account pk = do
    let inst = scriptInstance account
    utxos <- utxoAt (Scripts.scriptAddress inst)
    let tx = TypedTx.collectFromScript utxos inst ()
    -- TODO. Replace 'PubKey' with a more general 'Address' type of output?
    --       Or perhaps add a field 'requiredTokens' to 'UnbalancedTx' and let the
    --       balancing mechanism take care of providing the token.
    pure $ tx & outputs .~ [pubKeyTxOut (accountToken account) pk]

-- | Empty the account by spending all outputs belonging to the 'Account'.
redeem
  :: ( AsContractError e
     , HasWriteTx s
     , HasUtxoAt s
     )
  => PubKey
  -- ^ Where the token should go after the transaction
  -> Account
  -- ^ The token account
  -> Contract s e TxId
redeem pk account = redeemTx account pk >>= submitTx

-- | @balance account@ returns the value of all unspent outputs that can be
--   unlocked with @accountToken account@
balance
    :: ( HasUtxoAt s )
    => Account
    -> Contract s e Value
balance account = do
    utxos <- utxoAt (address account)
    let inner =
            foldMap (view Ledger.outValue . Ledger.txOutTxOut)
            $ fromMaybe Map.empty
            $ utxos ^. at (address account)
    pure inner

-- | Create a new token and return its 'Account' information.
newAccount
    :: ( HasWatchAddress s
       , HasWriteTx s
       , AsContractError e
       )
    => TokenName
    -- ^ Name of the token
    -> PubKey
    -- ^ Public key of the token's initial owner
    -> Contract s e Account
newAccount tokenName pk = do
    cur <- Currency.forgeContract pk [(tokenName, 1)]
    let sym = Ledger.scriptCurrencySymbol (Currency.curValidator cur)
    pure $ Account (sym, tokenName)

-- | Check that the balance of the given account satisfies a predicate.
assertAccountBalance
    :: forall s e a.
       Account
    -> (Value -> Bool)
    -> TracePredicate s e a
assertAccountBalance account check = fundsAtAddress (address account) check

PlutusTx.makeLift ''Account
PlutusTx.makeIsData ''Account
