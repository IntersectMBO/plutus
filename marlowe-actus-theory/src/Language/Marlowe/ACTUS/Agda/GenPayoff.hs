module Language.Marlowe.ACTUS.Agda.GenPayoff where

import           Language.Marlowe.ACTUS.Model.POF.PayoffModel

import           Language.Marlowe.ACTUS.Definitions.ContractTerms
import           Language.Marlowe.ACTUS.Agda.AgdaGen
import           Language.Marlowe.ACTUS.Agda.AgdaOps
import           Agda.Syntax.Common                                    (NamedArg, MaybePlaceholder, ExpandedEllipsis(..), noPlaceholder, defaultNamedArg, defaultArgInfo, defaultArg)
import           Agda.Syntax.Position                                  (Range'(..))
import           Agda.Syntax.Literal                                   (Literal(..))
import           Agda.Syntax.Concrete                                  (Expr(..), OpApp(..), Declaration(..), WhereClause'(..), LHS(..), RHS'(..), Pattern(..))
import           Agda.Syntax.Concrete.Name                             (Name(..), QName(..), NameInScope(..), NamePart(..))
import           Data.List.NonEmpty                                    (NonEmpty(..))
import           Agda.Utils.List2                                      (List2(..))
import           Control.Monad                                         (join)

numberType :: String
numberType = "ℤ"

payoff :: Declaration
payoff = genModule "POF" (imports ++ defs) where
    _POF_PY_PAM_PYTP_A = _POF_PY_PAM PYTP_A o_rf_CURS o_rf_RRMO _PYRT _cPYRT _CNTRL nt ipnr y_sd_t
    _POF_PY_PAM_PYTP_N = _POF_PY_PAM PYTP_N o_rf_CURS o_rf_RRMO _PYRT _cPYRT _CNTRL nt ipnr y_sd_t
    _POF_PY_PAM_PYTP_I = _POF_PY_PAM PYTP_I o_rf_CURS o_rf_RRMO _PYRT _cPYRT _CNTRL nt ipnr y_sd_t
    _POF_PY_PAM_PYTP_O = _POF_PY_PAM PYTP_O o_rf_CURS o_rf_RRMO _PYRT _cPYRT _CNTRL nt ipnr y_sd_t
    _POF_PY_PAM_param1 = "o_rf_CURS" 
    _POF_PY_PAM_params = ["o_rf_RRMO", "_PYRT", "_cPYRT", "_CNTRL", "nt", "ipnr", "y_sd_t"]
    _POF_PY_PAM_types = replicate (1 + length _POF_PY_PAM_params) numberType
    defs = join
        [ genDefinition _POF_PY_PAM_PYTP_A "_POF_PY_PAM_PYTP_A" _POF_PY_PAM_param1 _POF_PY_PAM_params _POF_PY_PAM_types numberType
        , genDefinition _POF_PY_PAM_PYTP_N "_POF_PY_PAM_PYTP_N" _POF_PY_PAM_param1 _POF_PY_PAM_params _POF_PY_PAM_types numberType
        , genDefinition _POF_PY_PAM_PYTP_I "_POF_PY_PAM_PYTP_I" _POF_PY_PAM_param1 _POF_PY_PAM_params _POF_PY_PAM_types numberType
        , genDefinition _POF_PY_PAM_PYTP_O "_POF_PY_PAM_PYTP_O" _POF_PY_PAM_param1 _POF_PY_PAM_params _POF_PY_PAM_types numberType
        ]
    o_rf_CURS = ident "o_rf_CURS"
    o_rf_RRMO = ident "o_rf_RRMO"
    _PYRT = ident "_PYRT"
    _cPYRT = ident "_cPYRT"
    _CNTRL = ident "_CNTRL"
    nt = ident "nt"
    ipnr = ident "ipnr"
    y_sd_t = ident "y_sd_t"
    imports = genImport <$> ["Data.Integer", "Definitions", "Utils"]