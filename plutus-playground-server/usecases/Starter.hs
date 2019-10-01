{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
module Starter where
-- TRIM TO HERE
-- This is a starter contract, based on the Game contract,
-- containing the bare minimum required scaffolding.
--
-- What you should change to something more suitable for
-- your use case:
--   * The DataScript type
--   * The Redeemer type
--
-- And add function implementations (and rename them to
-- something suitable) for the endpoints:
--   * publish
--   * redeem

import qualified Language.PlutusTx          as PlutusTx
import           Language.PlutusTx.Prelude  hiding (Applicative (..))
import           Ledger                     (Address, DataScript (DataScript), PendingTx,
                                             RedeemerScript (RedeemerScript), ValidatorScript (ValidatorScript),
                                             compileScript, scriptAddress, lifted)
import           Ledger.Value               (Value)
import           Playground.Contract
import           Wallet                     (MonadWallet, WalletAPI, WalletDiagnostics, collectFromScript,
                                             defaultSlotRange, payToScript_, startWatching)

-- | These are the data script and redeemer types. We are using an integer
--   value for both, but you should define your own types.
data DataValue = DataValue Integer
PlutusTx.makeLift ''DataValue

data RedeemerValue = RedeemerValue Integer
PlutusTx.makeLift ''RedeemerValue

-- | This method is the spending validator (which gets lifted to
--   its on-chain representation).
validateSpend :: DataValue -> RedeemerValue -> PendingTx -> Bool
validateSpend _dataValue _redeemerValue _ = error () -- Please provide an implementation.

-- | This function lifts the validator previously defined to
--   the on-chain representation.
contractValidator :: ValidatorScript
contractValidator =
    ValidatorScript ($$(Ledger.compileScript [|| validateSpend ||]))

-- | Helper function used to build the DataScript.
mkDataScript :: Integer -> DataScript
mkDataScript =
    DataScript . lifted . DataValue

-- | Helper function used to build the RedeemerScript.
mkRedeemerScript :: Integer -> RedeemerScript
mkRedeemerScript =
    RedeemerScript . lifted . RedeemerValue

-- | The address of the contract (the hash of its validator script).
contractAddress :: Address
contractAddress = Ledger.scriptAddress contractValidator

-- | The "publish" contract endpoint.
publish :: MonadWallet m => Integer -> Value -> m ()
publish dataValue lockedFunds  =
    payToScript_ defaultSlotRange contractAddress lockedFunds (mkDataScript dataValue)

-- | The "redeem" contract endpoint.
redeem :: (WalletAPI m, WalletDiagnostics m) => Integer -> m ()
redeem redeemerValue = do
    let redeemer = mkRedeemerScript redeemerValue
    collectFromScript defaultSlotRange contractValidator redeemer

-- | The "start" contract endpoint, telling the wallet to start watching
--   the address of the script.
start :: MonadWallet m => m ()
start =
    startWatching contractAddress

$(mkFunctions ['publish, 'redeem, 'start])
