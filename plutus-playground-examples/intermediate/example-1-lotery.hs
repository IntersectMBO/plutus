{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings   #-}
module Lottery where

import           PlutusTx
import           PlutusTx.Prelude
import           Ledger
import           Ledger.Typed.Scripts
import           Ledger.Value

data LotteryDatum = LotteryDatum
    { participants :: [PubKeyHash]
    , winner :: Maybe PubKeyHash
    } deriving Show

PlutusTx.unstableMakeIsData ''LotteryDatum

data Lottery
instance Scripts.ValidatorTypes Lottery where
    type instance DatumType Lottery = LotteryDatum
    type instance RedeemerType Lottery = ()

lotteryValidator :: LotteryDatum -> () -> ScriptContext -> Bool
lotteryValidator datum _ ctx =
    case winner datum of
        Nothing -> traceIfFalse "No winner yet" False
        Just p  -> True

typedLotteryValidator :: Scripts.TypedValidator Lottery
typedLotteryValidator = Scripts.mkTypedValidator @Lottery
    $$(PlutusTx.compile [|| lotteryValidator ||])
    $$(PlutusTx.compile [|| wrap ||])
  where
    wrap = Scripts.wrapValidator @LotteryDatum @()
