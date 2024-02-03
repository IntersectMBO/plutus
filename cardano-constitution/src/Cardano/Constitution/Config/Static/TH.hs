{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns    #-}
module Cardano.Constitution.Config.Static.TH
    ( ConstitutionConfigStatic (..)
    , toConfigStatic
    ) where

import Cardano.Constitution.Config.Predicate
import Cardano.Constitution.Config.Types
import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.SortedMap qualified as SortedMap

import Language.Haskell.TH as TH

{- | A map of param-ids to a list of predicate functions.

Normally, each predicate in the list have to be `and`ed together by the validator script.
Alternatively, as Kenneth pointed out we could `and` them already in TH, but then we would lose
the feature of tracing back which particular predicate failed.
-}
newtype ConstitutionConfigStatic = ConstitutionConfigStatic
    {
        unConstitutionConfigStatic :: SortedMap.SortedMap ParamId [PredMeaningApplied]
    }

-- TODO: replace the following two with *Typed* TH;
-- it is difficult because of TH.Names and Lists

toConfigStatic :: ConstitutionConfig -> Q Exp
toConfigStatic (unConstitutionConfig -> SortedMap.toList -> cfgAlist) =
  [| ConstitutionConfigStatic (SortedMap.fromListSafe $(listE (fmap (\(pid, pconfig) ->
                                                 [|(pid, $(toParamConfigStatic pconfig) )|])
                                                    cfgAlist))
                              )
   |]

toParamConfigStatic :: ParamConfig -> Q Exp
toParamConfigStatic (unParamConfig -> AssocMap.toList -> predAlist) = listE $ flip fmap predAlist $
    \(predName, expectedPredValue) ->
        case AssocMap.lookup predName defaultPredMeaningsUnresolved of
            Nothing         -> fail "Config contains an uknown pred name"
            Just thPredName -> [| $(varE thPredName) expectedPredValue :: PredMeaningApplied |]
