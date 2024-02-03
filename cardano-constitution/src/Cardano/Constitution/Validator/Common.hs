{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns    #-}
module Cardano.Constitution.Validator.Common
    ( ChangedParamsMap
    , pattern GetChangedParamsMap
    , ConstitutionValidator
    , toUntyped
    )
where

import Cardano.Constitution.Config.Predicate
import Cardano.Constitution.Config.Types

import PlutusLedgerApi.V3 as V3
import PlutusTx as Tx
import PlutusTx.AssocMap as Tx
import PlutusTx.Prelude as Tx hiding (toList)

type ChangedParamsMap = Tx.Map ParamId PredValue

pattern GetChangedParamsMap :: ChangedParamsMap -> ScriptContext
pattern GetChangedParamsMap cparams <-
    (scriptContextPurpose ->
        -- Is _pId needed?
        Proposing _pId (ppGovernanceAction ->
                         -- Is _gId needed?
                         ParameterChange _gId (ChangedParameters
                                               -- is _cHash needed?
                                               (Tx.unsafeFromBuiltinData -> cparams)) _cHash))

type ConstitutionValidator = () -- ^ unit (empty) redeemer
                           -> V3.ScriptContext -- ^ deep inside is the changed-parameters proposal
                           -> Bool -- ^ True means the proposal conforms to the constitution

{-# INLINABLE toUntyped #-}
toUntyped :: ConstitutionValidator -> (BuiltinData -> BuiltinData -> ())
toUntyped cVldtr (Tx.unsafeFromBuiltinData -> rdmr) (Tx.unsafeFromBuiltinData -> ctx) =
    Tx.check (cVldtr rdmr ctx)
