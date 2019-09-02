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
  , payTx
  -- * Endpoints
  , TokenAccountSchema
  , HasTokenAccountSchema
  , tokenAccountContract
  -- * Etc.
  , assertAccountBalance
  , validatorHash
  ) where

import           Control.Lens
import           Control.Monad                                     (unless, void)
import           Control.Monad.Writer                              (tell)
import qualified Data.Map                                          as Map
import           Data.Maybe                                        (fromMaybe)
import           Data.Text.Prettyprint.Doc

import           Language.Plutus.Contract
import qualified Language.PlutusTx                                 as PlutusTx

import qualified Language.Plutus.Contract.Typed.Tx                 as TypedTx
import           Language.Plutus.Contract.Test                     (TracePredicate, PredF(..))
import           Language.Plutus.Contract.Trace                    as Trace
import           Ledger                                            (Address, PubKey, TxOutTx (..), ValidatorHash)
import qualified Ledger.AddressMap                                 as AM
import qualified Ledger                                            as Ledger
import           Ledger.TxId                                       (TxId)
import           Ledger.Typed.Scripts                              (ScriptType (..))
import qualified Ledger.Typed.Scripts                              as Scripts
import qualified Ledger.Validation                                 as V
import           Ledger.Value                                      (CurrencySymbol, TokenName, Value)
import qualified Ledger.Value                                      as Value
import qualified Wallet.Emulator                                   as EM

import qualified Language.PlutusTx.Coordination.Contracts.Currency as Currency

newtype AccountOwner = AccountOwner { unAccountOwner :: (CurrencySymbol, TokenName) }
    deriving newtype (Eq, Show)

instance Pretty AccountOwner where
    pretty (AccountOwner (s, t)) = pretty s <+> pretty t

data TokenAccount

instance ScriptType TokenAccount where
    type RedeemerType TokenAccount = ()
    type DataType TokenAccount = ()

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
validate :: AccountOwner -> () -> () -> V.PendingTx -> Bool
validate owner _ _ ptx = V.valueSpent ptx `Value.geq` accountToken owner

scriptInstance :: AccountOwner -> Scripts.ScriptInstance TokenAccount
scriptInstance owner =
    let wrap = Scripts.wrapValidator @() @()
        val = $$(PlutusTx.compile [|| validate ||])
                `PlutusTx.applyCode`
                    PlutusTx.liftCode owner

    in Scripts.Validator @TokenAccount 
        val
        $$(PlutusTx.compile [|| wrap ||])    

address :: AccountOwner -> Address
address = Scripts.scriptAddress . scriptInstance

validatorHash :: AccountOwner -> ValidatorHash
validatorHash = Scripts.validatorHash . scriptInstance

payTx :: AccountOwner -> Value -> UnbalancedTx
payTx owner vl = 
    let ds = Ledger.DataScript (PlutusTx.toData ())
    in payToScript vl (address owner) ds

-- | Pay some money to the given token account
pay :: (AsContractError e, HasWriteTx s) => AccountOwner -> Value -> Contract s e TxId
pay owner = writeTxSuccess . payTx owner

-- | Create a transaction that spends all outputs belonging to the 'AccountOwner'.
redeemTx
    :: ( HasUtxoAt s )
    => AccountOwner
    -> PubKey
    -> Contract s e UnbalancedTx
redeemTx owner pk = do
    utxos <- utxoAt (address owner)
    let tx = TypedTx.collectFromScript utxos (scriptInstance owner) ()
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
    utxos <- utxoAt (address owner)
    let inner =
            foldMap (view Ledger.outValue . Ledger.txOutTxOut)
            $ fromMaybe Map.empty
            $ utxos ^. at (address owner)
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

assertAccountBalance
    :: forall s e a.
       AccountOwner
    -> (Value -> Bool)
    -> TracePredicate s e a
assertAccountBalance owner check = PredF $ \(_, r) -> do
    let funds =
            foldMap (view Ledger.outValue . Ledger.txOutTxOut)
            $ fromMaybe Map.empty
            $ view (at (address owner))
            $ AM.fromChain
            $ view EM.chainOldestFirst 
            $ Trace._ctrEmulatorState r
        passes = check funds
    unless passes
        $ tell ("Funds owned by " <+> pretty owner <+> "were" <> pretty funds)
    pure passes

PlutusTx.makeLift ''AccountOwner
PlutusTx.makeIsData ''AccountOwner
