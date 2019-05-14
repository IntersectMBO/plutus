{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
module Tutorial.Solutions2 where

import qualified Data.Map                     as Map

import qualified Language.PlutusTx            as P
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
import qualified Tutorial.Solutions1            as TH
import Tutorial.Emulator (SecretNumber(..), ClearNumber(..))

{-

    E2.

    >>> import qualified Language.PlutusTx.Plugin as PL
    >>> PL.sizePlc trickier2
    979
    >>> PL.sizePlc trickier5
    2176
    >>> PL.sizePlc trickier10
    4171

-}


{-

    E3*.

    >>> PL.sizePlc trickier10Light
    3799
-}
trickier10Light :: P.CompiledCode (Integer -> Integer)
trickier10Light = $$(P.compile [|| $$(TH.trickierLight 10) ||])

{-

    E4 (validator script)

-}
intGameValidator :: ValidatorScript
intGameValidator = ValidatorScript ($$(L.compileScript [||
  \(SecretNumber actual) (ClearNumber guess') (_ :: PendingTx) ->
    if $$(P.eq) actual ($$(TH.trickier 2) guess')
    then ()
    else $$(P.error) ($$(P.traceH) "Wrong number" ())
  ||]))

gameAddress :: Address
gameAddress = L.scriptAddress intGameValidator

{-

      E4 (lock endpoint) Note how we use the same TH quote, $$(TH.trickier 2),
      in on-chain and off-chain code. This is how code can be shared between
      the two. Write once, run anywhere!

-}
lock :: (WalletAPI m, WalletDiagnostics m) => Integer -> Ada -> m ()
lock i adaVl = do
    let secretInt = $$(TH.trickier 2) i
        vl = Ada.toValue adaVl
        ds = DataScript (L.lifted (SecretNumber secretInt))
    W.payToScript_ W.defaultSlotRange gameAddress vl ds
