module Language.Marlowe.ACTUS.Agda.GenStateTransition(stateTransition) where

import           Language.Marlowe.ACTUS.Model.STF.StateTransitionModel

import           Agda.Syntax.Common                                    (ExpandedEllipsis (..), MaybePlaceholder,
                                                                        NamedArg, defaultArg, defaultArgInfo,
                                                                        defaultNamedArg, noPlaceholder)
import           Agda.Syntax.Concrete                                  (Declaration (..), Expr (..), LHS (..),
                                                                        OpApp (..), Pattern (..), RHS' (..),
                                                                        WhereClause' (..))
import           Agda.Syntax.Concrete.Name                             (Name (..), NameInScope (..), NamePart (..),
                                                                        QName (..))
import           Agda.Syntax.Literal                                   (Literal (..))
import           Agda.Syntax.Position                                  (Range' (..))
import           Agda.Utils.List2                                      (List2 (..))
import           Control.Monad                                         (join)
import           Data.List.NonEmpty                                    (NonEmpty (..))
import           Language.Marlowe.ACTUS.Agda.AgdaGen
import           Language.Marlowe.ACTUS.Agda.AgdaOps
import           Language.Marlowe.ACTUS.Definitions.ContractState
import           Language.Marlowe.ACTUS.Definitions.ContractTerms

numberType :: String
numberType = "ℤ"

previousState :: ContractStatePoly Expr Expr
previousState =
    ContractStatePoly {
        tmd = genAccessor "tmd"
        , nt = genAccessor "nt"
        , ipnr = genAccessor "ipnr"
        , ipac = genAccessor "ipac"
        , feac = genAccessor "feac"
        , fac = genAccessor "fac"
        , nsc = genAccessor "nsc"
        , isc = genAccessor "isc"
        , sd = genAccessor "sd"
        , prnxt = genAccessor "prnxt"
        , ipcb = genAccessor "ipcb"
    } where
        genAccessor varName =
            Paren NoRange $ App NoRange (Ident $ QName $ quickname ("ContractState." ++ varName)) (defaultNamedArg $ ident "st")
        quickname op = Name NoRange NotInScope $ (Id op) :| []

-- for every state variable - we generate specialised state transition function
genStateTransitionsForStateVariables :: (ContractStatePoly Expr Expr) -> String -> String -> [String] -> [String] -> [Declaration]
genStateTransitionsForStateVariables nextState functionName param1 params types =
    join [
      genDefinition (tmd nextState) (mkFunctionName "tmd") param1 params types numberType
    , genDefinition (nt nextState) (mkFunctionName "nt") param1 params types numberType
    , genDefinition (ipnr nextState) (mkFunctionName "ipnr") param1 params types numberType
    , genDefinition (ipac nextState) (mkFunctionName "ipac") param1 params types numberType
    , genDefinition (feac nextState) (mkFunctionName "feac") param1 params types numberType
    , genDefinition (fac nextState) (mkFunctionName "fac") param1 params types numberType
    , genDefinition (nsc nextState) (mkFunctionName "nsc") param1 params types numberType
    , genDefinition (isc nextState) (mkFunctionName "isc") param1 params types numberType
    , genDefinition (isc nextState) (mkFunctionName "sd") param1 params types numberType
    , genDefinition (isc nextState) (mkFunctionName "prnxt") param1 params types numberType
    , genDefinition (isc nextState) (mkFunctionName "ipcb") param1 params types numberType
    ]
    where mkFunctionName stateVarName = functionName ++ "_" ++ stateVarName


stateTransition :: Declaration
stateTransition = genModule "Generated.StateTransition" (imports ++ defs) where
    _STF_IED_PAM_state_ALL = _STF_IED_PAM previousState t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    _STF_IED_PAM_state_IPNR_IPANX = _STF_IED_PAM previousState t y_ipanx_t _IPNR _IPANX _CNTRL Nothing _NT
    _STF_IED_PAM_state_IPNR_IPAC = _STF_IED_PAM previousState t y_ipanx_t _IPNR Nothing _CNTRL _IPAC _NT
    _STF_IED_PAM_state_IPAC_IPANX = _STF_IED_PAM previousState t y_ipanx_t Nothing _IPANX _CNTRL _IPAC _NT
    _STF_IED_PAM_state_IPAC = _STF_IED_PAM previousState t y_ipanx_t Nothing Nothing _CNTRL _IPAC _NT
    _STF_IED_PAM_state_IPANX = _STF_IED_PAM previousState t y_ipanx_t Nothing _IPANX _CNTRL Nothing _NT
    _STF_IED_PAM_state_IPNR = _STF_IED_PAM previousState t y_ipanx_t _IPNR Nothing _CNTRL Nothing _NT
    _STF_IED_PAM_param1 = "st"
    _STF_IED_PAM_params = ["t", "y_ipanx_t", "_IPNR", "_IPANX", "_CNTRL", "_IPAC", "_NT"]
    _STF_IED_PAM_types = "ContractState" : replicate (length _STF_IED_PAM_params) numberType
    defs = join
        [ genStateTransitionsForStateVariables _STF_IED_PAM_state_ALL "_STF_IED_PAM_ALL" _STF_IED_PAM_param1 _STF_IED_PAM_params _STF_IED_PAM_types
        , genStateTransitionsForStateVariables _STF_IED_PAM_state_IPNR_IPANX "_STF_IED_PAM_IPNR_IPANX" _STF_IED_PAM_param1 _STF_IED_PAM_params _STF_IED_PAM_types
        , genStateTransitionsForStateVariables _STF_IED_PAM_state_IPNR_IPAC "_STF_IED_PAM_IPNR_IPAC" _STF_IED_PAM_param1 _STF_IED_PAM_params _STF_IED_PAM_types
        , genStateTransitionsForStateVariables _STF_IED_PAM_state_IPAC_IPANX "_STF_IED_PAM_IPAC_IPANX" _STF_IED_PAM_param1 _STF_IED_PAM_params _STF_IED_PAM_types
        , genStateTransitionsForStateVariables _STF_IED_PAM_state_IPAC "_STF_IED_PAM_IPAC" _STF_IED_PAM_param1 _STF_IED_PAM_params _STF_IED_PAM_types
        , genStateTransitionsForStateVariables _STF_IED_PAM_state_IPANX "_STF_IED_PAM_IPANX" _STF_IED_PAM_param1 _STF_IED_PAM_params _STF_IED_PAM_types
        , genStateTransitionsForStateVariables _STF_IED_PAM_state_IPNR "_STF_IED_PAM_IPNR" _STF_IED_PAM_param1 _STF_IED_PAM_params _STF_IED_PAM_types
        ]
    t = ident "t"
    y_ipanx_t = ident "y_ipanx_t"
    _IPNR = Just $ ident "_IPNR"
    _IPANX = Just $ ident "_IPANX"
    _IPAC = Just $ ident "_IPAC"
    _CNTRL = ident "_CNTRL"

    _NT = ident "_NT"
    imports = genImport <$> ["Data.Integer", "Definitions", "Utils"]
