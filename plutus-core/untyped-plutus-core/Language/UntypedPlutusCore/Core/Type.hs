{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.UntypedPlutusCore.Core.Type
    ( TPLC.UniOf
    , TPLC.Version (..)
    , Term (..)
    , Program (..)
    , toTerm
    , erase
    , eraseWith
    , eraseProgram
    , eraseProgramWith
    ) where

import           PlutusPrelude

import qualified Language.PlutusCore.Constant                       as TPLC
import qualified Language.PlutusCore.Core                           as TPLC
import           Language.PlutusCore.Core.Type                      (HasAnnotation)
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import qualified Language.PlutusCore.Name                           as TPLC
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
data Term name uni fun ann
    = Constant ann (Some (ValueOf uni))
    | Builtin ann fun
    | Var ann name
    | LamAbs ann name (Term name uni fun ann)
    | Apply ann (Term name uni fun ann) (Term name uni fun ann)
    | Delay ann (Term name uni fun ann)
    | Force ann (Term name uni fun ann)
    | Error ann
    deriving stock (Show, Functor, Generic)
    deriving anyclass (NFData)

-- | A 'Program' is simply a 'Term' coupled with a 'Version' of the core language.
data Program name uni fun ann = Program ann (TPLC.Version ann) (Term name uni fun ann)
    deriving stock (Show, Functor, Generic)
    deriving anyclass (NFData)

type instance TPLC.UniOf (Term name uni fun ann) = uni

instance TPLC.AsConstant (Term name uni fun ann) where
    asConstant (Constant _ val) = Just val
    asConstant _                = Nothing

instance TPLC.FromConstant (Term name uni fun ()) where
    fromConstant = Constant ()

type instance TPLC.HasUniques (Term name uni fun ann) = TPLC.HasUnique name TPLC.TermUnique
type instance TPLC.HasUniques (Program name uni fun ann) = TPLC.HasUniques (Term name uni fun ann)

instance ToExMemory (Term name uni fun ()) where
    toExMemory _ = 0

instance ToExMemory (Term name uni fun ExMemory) where
    toExMemory = termAnn

instance HasAnnotation (Term name uni fun ann) where
    type Annotation (Term name uni fun ann) = ann
    toAnnotation = termAnn

deriving via GenericExMemoryUsage (Term name uni fun ann) instance
    ( ExMemoryUsage name, ExMemoryUsage fun, ExMemoryUsage ann
    , Closed uni, uni `Everywhere` ExMemoryUsage
    ) => ExMemoryUsage (Term name uni fun ann)

toTerm :: Program name uni fun ann -> Term name uni fun ann
toTerm (Program _ _ term) = term

-- | Return the outermost annotation of a 'Term'.
termAnn :: Term name uni fun ann -> ann
termAnn (Constant ann _) = ann
termAnn (Builtin ann _)  = ann
termAnn (Var ann _)      = ann
termAnn (LamAbs ann _ _) = ann
termAnn (Apply ann _ _)  = ann
termAnn (Delay ann _)    = ann
termAnn (Force ann _)    = ann
termAnn (Error ann)      = ann

-- | Erase a Typed Plutus Core term to its untyped counterpart.
erase :: TPLC.Term tyname name uni fun () -> Term name uni fun ()
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

-- TODO proper recursion so the translation function can use `TPLC.Term name uni fun untypedAnn`
eraseWith :: (ann -> untypedAnn) -> TPLC.Term tyname name uni fun ann -> Term name uni fun untypedAnn
eraseWith f (TPLC.Var ann name)           = Var (f ann) name
eraseWith f (TPLC.TyAbs ann _ _ body)     = Delay (f ann) (eraseWith f body)
eraseWith f (TPLC.LamAbs ann name _ body) = LamAbs (f ann) name (eraseWith f body)
eraseWith f (TPLC.Apply ann fun arg)      = Apply (f ann) (eraseWith f fun) (eraseWith f arg)
eraseWith f (TPLC.Constant ann con)       = Constant (f ann) con
eraseWith f (TPLC.Builtin ann bn)         = Builtin (f ann) bn
eraseWith f (TPLC.TyInst ann term _)      = Force (f ann) (eraseWith f term)
eraseWith f (TPLC.Unwrap _ term)          = eraseWith f term
eraseWith f (TPLC.IWrap _ _ _ term)       = eraseWith f term
eraseWith f (TPLC.Error ann _)            = Error (f ann)

-- | Erase a Typed Plutus Core Program to its untyped counterpart.
eraseProgram :: TPLC.Program tyname name uni fun () -> Program name uni fun ()
eraseProgram (TPLC.Program a v t) = Program a v $ erase t

eraseProgramWith :: (ann -> untypedAnn) -> TPLC.Program tyname name uni fun ann -> Program name uni fun untypedAnn
eraseProgramWith fun (TPLC.Program a v t) = Program (fun a) (fmap fun v) $ eraseWith fun t
