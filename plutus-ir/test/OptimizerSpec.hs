{-# LANGUAGE OverloadedStrings #-}
module OptimizerSpec where

import           Common
import           TestLib

import           Language.PlutusCore.Quote

import           Language.PlutusIR
import           Language.PlutusIR.MkPir
import           Language.PlutusIR.Optimizer.DeadCode

import qualified Language.PlutusCore                  as PLC

import qualified Language.PlutusCore.StdLib.Data.Unit as Unit

optimizer :: TestNested
optimizer = testNested "optimizer" [
    deadCode
    ]

deadCode :: TestNested
deadCode = testNested "deadCode" [
    goldenPir "typeLet" (runQuote typeLet)
    , goldenPir "termLet" (runQuote termLet)
    , goldenPir "datatypeLiveType" (runQuote datatypeLiveType)
    , goldenPir "datatypeLiveConstr" (runQuote datatypeLiveConstr)
    , goldenPir "datatypeLiveDestr" (runQuote datatypeLiveDestr)
    , goldenPir "datatypeDead" (runQuote datatypeDead)
    , goldenPir "singleBinding" (runQuote singleBinding)
    , goldenPir "nestedBindings" (runQuote nestedBindings)
    , goldenPir "nestedBindingsIndirect" (runQuote nestedBindingsIndirect)
    , goldenPir "recBindingSimple" (runQuote recBindingSimple)
    , goldenPir "recBindingComplex" (runQuote recBindingComplex)
    ]

typeLet :: Quote (Term TyName Name ())
typeLet = removeDeadBindings <$> do
    u <- freshTyName () "unit"
    unit <- Unit.getBuiltinUnit
    unitVal <- embedIntoIR <$> Unit.getBuiltinUnitval
    pure $ Let () NonRec [
        TypeBind () (TyVarDecl () u (PLC.Type ())) unit
        ] unitVal

termLet :: Quote (Term TyName Name ())
termLet = removeDeadBindings <$> do
    uv <- freshName () "unitval"
    unit <- Unit.getBuiltinUnit
    unitVal <- embedIntoIR <$> Unit.getBuiltinUnitval
    pure $ Let () NonRec [
        TermBind () (VarDecl () uv unit) unitVal
        ] unitVal

datatypeLiveType :: Quote (Term TyName Name ())
datatypeLiveType = removeDeadBindings <$> do
    mb@(Datatype _ d _ _ _) <- maybeDatatype

    pure $
        Let ()
            NonRec
            [
                DatatypeBind () mb
            ] (Error () (mkTyVar () d))

datatypeLiveConstr :: Quote (Term TyName Name ())
datatypeLiveConstr = removeDeadBindings <$> do
    mb@(Datatype _ _ _ _ [nothing, _]) <- maybeDatatype

    pure $
        Let ()
            NonRec
            [
                DatatypeBind () mb
            ] (mkVar () nothing)

datatypeLiveDestr :: Quote (Term TyName Name ())
datatypeLiveDestr = removeDeadBindings <$> do
    mb@(Datatype _ _ _ match _) <- maybeDatatype

    pure $
        Let ()
            NonRec
            [
                DatatypeBind () mb
            ] (Var () match)

datatypeDead :: Quote (Term TyName Name ())
datatypeDead = removeDeadBindings <$> do
    mb <- maybeDatatype
    unitVal <- embedIntoIR <$> Unit.getBuiltinUnitval

    pure $
        Let ()
            NonRec
            [
                DatatypeBind () mb
            ] unitVal

singleBinding :: Quote (Term TyName Name ())
singleBinding = removeDeadBindings <$> do
    u <- freshTyName () "unit"
    uv <- freshName () "unitval"
    unit <- Unit.getBuiltinUnit
    unitVal <- embedIntoIR <$> Unit.getBuiltinUnitval
    pure $ Let () NonRec [
        TypeBind () (TyVarDecl () u (PLC.Type ())) unit,
        TermBind () (VarDecl () uv unit) unitVal
        ] (Var () uv)

nestedBindings :: Quote (Term TyName Name ())
nestedBindings = removeDeadBindings <$> do
    u <- freshTyName () "unit"
    uv <- freshName () "unitval"
    unit <- Unit.getBuiltinUnit
    unitVal <- embedIntoIR <$> Unit.getBuiltinUnitval
    pure $
        Let () NonRec [
        TypeBind () (TyVarDecl () u (PLC.Type ())) unit
        ] $
        Let () NonRec [
        TermBind () (VarDecl () uv unit) unitVal
        ] (Var () uv)

nestedBindingsIndirect :: Quote (Term TyName Name ())
nestedBindingsIndirect = removeDeadBindings <$> do
    u <- freshTyName () "unit"
    unit <- Unit.getBuiltinUnit

    dt <- freshTyName () "SomeType"
    match <- freshName () "match_SomeType"
    constr <- freshName () "Constr"

    arg <- freshName () "arg"
    pure $
        Let () NonRec [
        -- only used by the constructor of dt, needs to not be removed
        TypeBind () (TyVarDecl () u (PLC.Type ())) unit
        ] $
        Let () NonRec [
        DatatypeBind () (Datatype ()
            (TyVarDecl () dt (PLC.Type ()))
            []
            match
            -- this is live because dt is
            [VarDecl () constr (TyFun () (TyVar () u) (TyVar () dt))])
        -- uses dt
        ] (LamAbs () arg (TyVar () dt) (Var () arg))

recBindingSimple :: Quote (Term TyName Name ())
recBindingSimple = removeDeadBindings <$> do
    uv <- freshName () "unitval"
    unit <- Unit.getBuiltinUnit
    unitVal <- embedIntoIR <$> Unit.getBuiltinUnitval
    pure $ Let () Rec [
        TermBind () (VarDecl () uv unit) unitVal
        ] unitVal

recBindingComplex :: Quote (Term TyName Name ())
recBindingComplex = removeDeadBindings <$> do
    u <- freshTyName () "unit"
    uv <- freshName () "unitval"
    unit <- Unit.getBuiltinUnit
    unitVal <- embedIntoIR <$> Unit.getBuiltinUnitval
    pure $ Let () Rec [
        TypeBind () (TyVarDecl () u (PLC.Type ())) unit,
        TermBind () (VarDecl () uv unit) unitVal
        ] (Var () uv)
