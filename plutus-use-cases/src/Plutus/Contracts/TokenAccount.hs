{-# LANGUAGE ConstraintKinds    #-}
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}
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
  , redeemTx
  -- * Endpoints
  , TokenAccountSchema
  , HasTokenAccountSchema
  , tokenAccountContract
  -- * Etc.
  , TokenAccount
  , TokenAccountError(..)
  , AsTokenAccountError(..)
  , validatorHash
  , scriptInstance
  ) where

import           Control.Lens
import           Control.Monad                                     (void)
import           Control.Monad.Error.Lens
import           Data.Aeson                                        (FromJSON, ToJSON)
import qualified Data.Map                                          as Map
import           Data.Text.Prettyprint.Doc
import           GHC.Generics                                      (Generic)

import           Language.Plutus.Contract
import           Language.Plutus.Contract.Constraints
import qualified Language.PlutusTx                                 as PlutusTx

import qualified Language.Plutus.Contract.Typed.Tx                 as TypedTx
import           Ledger                                            (Address, PubKeyHash, Tx, TxOutTx (..),
                                                                    ValidatorHash)
import qualified Ledger                                            as Ledger
import qualified Ledger.Constraints                                as Constraints
import qualified Ledger.Contexts                                   as V
import qualified Ledger.Scripts
import           Ledger.Typed.Scripts                              (ScriptType (..))
import qualified Ledger.Typed.Scripts                              as Scripts
import           Ledger.Value                                      (CurrencySymbol, TokenName, Value)
import qualified Ledger.Value                                      as Value

import qualified Language.PlutusTx.Coordination.Contracts.Currency as Currency

newtype Account = Account { accountOwner :: (CurrencySymbol, TokenName) }
    deriving stock    (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)


instance Pretty Account where
    pretty (Account (s, t)) = pretty s <+> pretty t

data TokenAccount

instance ScriptType TokenAccount where
    type RedeemerType TokenAccount = ()
    type DatumType TokenAccount = ()

type TokenAccountSchema =
    BlockchainActions
        .\/ Endpoint "redeem" (Account, PubKeyHash)
        .\/ Endpoint "pay" (Account, Value)
        .\/ Endpoint "new-account" (TokenName, PubKeyHash)

type HasTokenAccountSchema s =
    ( HasBlockchainActions s
    , HasEndpoint "redeem" (Account, PubKeyHash) s
    , HasEndpoint "pay" (Account, Value) s
    , HasEndpoint "new-account" (TokenName, PubKeyHash) s
    )

data TokenAccountError =
    TAContractError ContractError
    | TACurrencyError Currency.CurrencyError
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

makeClassyPrisms ''TokenAccountError

instance AsContractError TokenAccountError where
    _ContractError = _TAContractError

instance Currency.AsCurrencyError TokenAccountError where
    _CurrencyError = _TACurrencyError

-- | 'transfer', 'redeem', 'pay' and 'newAccount' with endpoints.
tokenAccountContract
    :: forall w s e.
       ( HasTokenAccountSchema s
       , AsTokenAccountError e
       )
    => Contract w s e ()
tokenAccountContract = mapError (review _TokenAccountError) (redeem_ `select` pay_ `select` newAccount_) where
    redeem_ = do
        (accountOwner, destination) <- endpoint @"redeem" @(Account, PubKeyHash) @w @s
        void $ redeem destination accountOwner
        tokenAccountContract
    pay_ = do
        (accountOwner, value) <- endpoint @"pay" @_ @w @s
        void $ pay accountOwner value
        tokenAccountContract
    newAccount_ = do
        (tokenName, initialOwner) <- endpoint @"new-account" @_ @w @s
        void $ newAccount tokenName initialOwner
        tokenAccountContract

{-# INLINEABLE accountToken #-}
accountToken :: Account -> Value
accountToken (Account (symbol, name)) = Value.singleton symbol name 1

{-# INLINEABLE validate #-}
validate :: Account -> () -> () -> V.ValidatorCtx -> Bool
validate account _ _ ptx = V.valueSpent (V.valCtxTxInfo ptx) `Value.geq` accountToken account

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
    Value
    -> TxConstraints (Scripts.RedeemerType TokenAccount) (Scripts.DatumType TokenAccount)
payTx vl = Constraints.mustPayToTheScript () vl

-- | Pay some money to the given token account
pay
    :: ( HasWriteTx s
       , AsTokenAccountError e
       )
    => Account
    -> Value
    -> Contract w s e Tx
pay account vl = do
    let inst = scriptInstance account
    logInfo @String
        $ "TokenAccount.pay: Paying "
        <> show vl
        <> " into "
        <> show account
    mapError (review _TAContractError)
        $ submitTxConstraints inst
        $ payTx vl

-- | Create a transaction that spends all outputs belonging to the 'Account'.
redeemTx :: forall w s e.
    ( HasUtxoAt s
    , AsTokenAccountError e
    )
    => Account
    -> PubKeyHash
    -> Contract w s e (TxConstraints () (), ScriptLookups TokenAccount)
redeemTx account pk = mapError (review _TAContractError) $ do
    let inst = scriptInstance account
    utxos <- utxoAt (address account)
    let totalVal = foldMap (V.txOutValue . txOutTxOut) utxos
        numInputs = Map.size utxos
    logInfo @String
        $ "TokenAccount.redeemTx: Redeeming "
            <> show numInputs
            <> " outputs with a total value of "
            <> show totalVal
    let constraints = TypedTx.collectFromScript utxos ()
                <> Constraints.mustPayToPubKey pk (accountToken account)
        lookups = Constraints.scriptInstanceLookups inst
                <> Constraints.unspentOutputs utxos
    -- TODO. Replace 'PubKey' with a more general 'Address' type of output?
    --       Or perhaps add a field 'requiredTokens' to 'LedgerTxConstraints' and let the
    --       balancing mechanism take care of providing the token.
    pure (constraints, lookups)

-- | Empty the account by spending all outputs belonging to the 'Account'.
redeem
  :: ( HasWriteTx s
     , HasUtxoAt s
     , AsTokenAccountError e
     )
  => PubKeyHash
  -- ^ Where the token should go after the transaction
  -> Account
  -- ^ The token account
  -> Contract w s e Tx
redeem pk account = mapError (review _TokenAccountError) $ do
    (constraints, lookups) <- redeemTx account pk
    tx <- either (throwing _ConstraintResolutionError) pure (Constraints.mkTx lookups constraints)
    submitUnbalancedTx tx

-- | @balance account@ returns the value of all unspent outputs that can be
--   unlocked with @accountToken account@
balance
    :: ( HasUtxoAt s
       , AsTokenAccountError e
       )
    => Account
    -> Contract w s e Value
balance account = mapError (review _TAContractError) $ do
    utxos <- utxoAt (address account)
    let inner =
            foldMap (view Ledger.outValue . Ledger.txOutTxOut)
            $ utxos
    pure inner

-- | Create a new token and return its 'Account' information.
newAccount
    :: ( HasWriteTx s
       , HasTxConfirmation s
       , AsTokenAccountError e
       )
    => TokenName
    -- ^ Name of the token
    -> PubKeyHash
    -- ^ Public key of the token's initial owner
    -> Contract w s e Account
newAccount tokenName pk = mapError (review _TokenAccountError) $ do
    cur <- Currency.forgeContract pk [(tokenName, 1)]
    let sym = Currency.currencySymbol cur
    pure $ Account (sym, tokenName)

PlutusTx.makeLift ''Account
PlutusTx.unstableMakeIsData ''Account
