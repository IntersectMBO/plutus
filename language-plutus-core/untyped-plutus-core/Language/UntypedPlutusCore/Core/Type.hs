{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies      #-}

module Language.UntypedPlutusCore.Core.Type where

import           PlutusPrelude

import qualified Language.PlutusCore.Constant                       as TPLC
import qualified Language.PlutusCore.Core                           as TPLC
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Universe

data Term name uni ann
    = Constant ann (Some (ValueOf uni))
    | Builtin ann (TPLC.Builtin ann)
    | Var ann name
    | LamAbs ann name (Term name uni ann)
    | Apply ann (Term name uni ann) (Term name uni ann)
    | Delay ann (Term name uni ann)
    | Force ann (Term name uni ann)
    | Error ann
    deriving (Show, Functor, Generic)

type instance TPLC.UniOf (Term name uni ann) = uni

instance TPLC.AsConstant (Term name uni ann) where
    asConstant (Constant _ val) = Just val
    asConstant _                = Nothing

instance TPLC.FromConstant (Term name uni ()) where
    fromConstant = Constant ()

instance ToExMemory (Term name uni ()) where
    toExMemory _ = 0

instance ToExMemory (Term name uni ExMemory) where
    toExMemory = termAnn

termAnn :: Term name uni ann -> ann
termAnn (Constant ann _) = ann
termAnn (Builtin ann _)  = ann
termAnn (Var ann _)      = ann
termAnn (LamAbs ann _ _) = ann
termAnn (Apply ann _ _)  = ann
termAnn (Delay ann _)    = ann
termAnn (Force ann _)    = ann
termAnn (Error ann)      = ann

erase :: TPLC.Term tyname name uni ann -> Term name uni ann
erase (TPLC.Var ann name)           = Var ann name
erase (TPLC.TyAbs ann _ _ body)     = Delay ann (erase body)
erase (TPLC.LamAbs ann name _ body) = LamAbs ann name (erase body)
erase (TPLC.Apply ann fun arg)      = Apply ann (erase fun) (erase arg)
erase (TPLC.Constant ann con)       = Constant ann con
erase (TPLC.Builtin ann bn)         = Builtin ann bn
erase (TPLC.TyInst ann term _)      = Force ann (erase term)
erase (TPLC.Unwrap _ term)          = erase term
erase (TPLC.IWrap _ _ _ term)       = erase term
erase (TPLC.Error ann _)            = Error ann
