{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# LANGUAGE NoImplicitPrelude #-}
module Tutorial.Solutions1 where

import qualified Data.Map                     as Map

import qualified Language.PlutusTx            as PlutusTx
import           Language.PlutusTx.Prelude
import           Ledger                       (Address, DataScript(..), RedeemerScript(..), ValidatorScript(..), Value)
import qualified Ledger                       as L
import           Ledger.Validation            (PendingTx)
import qualified Ledger.Ada                   as Ada
import           Ledger.Ada                   (Ada)
import           Wallet                       (WalletAPI(..), WalletDiagnostics(..))
import qualified Wallet                       as W
import qualified Wallet.Emulator.Types        as EM
import qualified Wallet.API                   as WAPI

import qualified Tutorial.ExUtil                as EXU
import Tutorial.Emulator (SecretNumber(..), ClearNumber(..))

{-

    E1 (validator script)

-}
intGameValidator :: ValidatorScript
intGameValidator = ValidatorScript $$(L.compileScript [|| val ||])
    where
        val = \(SecretNumber actual) (ClearNumber guess') (_ :: PendingTx) -> actual `eq` (EXU.encode guess')

gameAddress :: Address
gameAddress = L.scriptAddress intGameValidator

{-

      E1 (lock endpoint) Note how we use the code, EXU.encode,
      in on-chain and off-chain code. This is how code can be shared between
      the two. Write once, run anywhere!

-}
lock :: (WalletAPI m, WalletDiagnostics m) => Integer -> Ada -> m ()
lock i adaVl = do
    let secretInt = EXU.encode i
        vl = Ada.toValue adaVl
        ds = DataScript (L.lifted (SecretNumber secretInt))
    W.payToScript_ W.defaultSlotRange gameAddress vl ds
