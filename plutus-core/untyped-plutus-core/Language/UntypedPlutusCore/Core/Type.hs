{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies      #-}

module Language.UntypedPlutusCore.Core.Type where

import           PlutusPrelude

import qualified Language.PlutusCore.Constant                       as TPLC
import qualified Language.PlutusCore.Core                           as TPLC
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Universe

-- | The type of Untyped Plutus Core terms. Mirrors the type of Typed Plutus Core terms except
--
-- 1. all types are removed
-- 2. 'IWrap' and 'Unwrap' are removed
-- 3. type abstractions are replaced with 'Delay'
-- 4. type instantiations are replaced with 'Force'
--
-- The latter two are due to the fact that we don't have value restriction in Typed Plutus Core
-- and hence a computation can be stuck expecting only a single type argument for the computation
-- to become unstuck. Therefore we can't just silently remove type abstractions and instantions and
-- need to replace them with something else that also blocks evaluation (in order for the semantics
-- of an erased program to match with the semantics of the original typed one). 'Delay' and 'Force'
-- serve exactly this purpose.
data Term name uni ann
    = Constant ann (Some (ValueOf uni))
    | Builtin ann TPLC.BuiltinName
    | Var ann name
    | LamAbs ann name (Term name uni ann)
    | Apply ann (Term name uni ann) (Term name uni ann)
    | Delay ann (Term name uni ann)
    | Force ann (Term name uni ann)
    | Error ann
    deriving (Show, Functor, Generic)

-- Instances needed by the constant application machinery.

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

-- | Return the outermost annotation of a 'Term'.
termAnn :: Term name uni ann -> ann
termAnn (Constant ann _) = ann
termAnn (Builtin ann _)  = ann
termAnn (Var ann _)      = ann
termAnn (LamAbs ann _ _) = ann
termAnn (Apply ann _ _)  = ann
termAnn (Delay ann _)    = ann
termAnn (Force ann _)    = ann
termAnn (Error ann)      = ann

-- | Erase a Typed Plutus Core term to its untyped counterpart.
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
