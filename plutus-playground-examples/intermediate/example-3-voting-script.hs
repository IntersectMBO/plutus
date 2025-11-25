
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings   #-}
module VotingContract where

import PlutusTx
import PlutusTx.Prelude
import Ledger
import Ledger.Typed.Scripts

data VoteDatum = VoteDatum
    { candidates :: [BuiltinByteString]
    , votes :: [(BuiltinByteString, Integer)]
    } deriving Show

PlutusTx.unstableMakeIsData ''VoteDatum

data Voting
instance Scripts.ValidatorTypes Voting where
    type instance DatumType Voting = VoteDatum
    type instance RedeemerType Voting = BuiltinByteString

votingValidator :: VoteDatum -> BuiltinByteString -> ScriptContext -> Bool
votingValidator datum candidate _ =
    candidate `elem` candidates datum

typedVotingValidator :: Scripts.TypedValidator Voting
typedVotingValidator = Scripts.mkTypedValidator @Voting
    $$(PlutusTx.compile [|| votingValidator ||])
    $$(PlutusTx.compile [|| wrap ||])
  where
    wrap = Scripts.wrapValidator @VoteDatum @BuiltinByteString
