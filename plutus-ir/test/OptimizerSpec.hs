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
    goldenPir "typeLet" typeLet
    , goldenPir "termLet" termLet
    , goldenPir "datatypeLiveType" datatypeLiveType
    , goldenPir "datatypeLiveConstr" datatypeLiveConstr
    , goldenPir "datatypeLiveDestr" datatypeLiveDestr
    , goldenPir "datatypeDead" datatypeDead
    , goldenPir "singleBinding" singleBinding
    , goldenPir "nestedBindings" nestedBindings
    , goldenPir "nestedBindingsIndirect" nestedBindingsIndirect
    , goldenPir "recBindingSimple" recBindingSimple
    , goldenPir "recBindingComplex" recBindingComplex
    ]

typeLet :: Term TyName Name ()
typeLet = runQuote $ removeDeadBindings <$> do
    u <- freshTyName () "unit"
    let unitVal = embedIntoIR Unit.unitval
    pure $ Let () NonRec [
        TypeBind () (TyVarDecl () u (PLC.Type ())) Unit.unit
        ] unitVal

termLet :: Term TyName Name ()
termLet = runQuote $ removeDeadBindings <$> do
    uv <- freshName () "unitval"
    let unitVal = embedIntoIR Unit.unitval
    pure $ Let () NonRec [
        TermBind () (VarDecl () uv Unit.unit) unitVal
        ] unitVal

datatypeLiveType :: Term TyName Name ()
datatypeLiveType = removeDeadBindings $
    let mb@(Datatype _ d _ _ _) = maybeDatatype
    in
        Let ()
            NonRec
            [
                DatatypeBind () mb
            ] (Error () (mkTyVar () d))

datatypeLiveConstr :: Term TyName Name ()
datatypeLiveConstr = removeDeadBindings $
    let mb@(Datatype _ _ _ _ [nothing, _]) = maybeDatatype
    in
        Let ()
            NonRec
            [
                DatatypeBind () mb
            ] (mkVar () nothing)

datatypeLiveDestr :: Term TyName Name ()
datatypeLiveDestr = removeDeadBindings $
    let mb@(Datatype _ _ _ match _) = maybeDatatype
    in
        Let ()
            NonRec
            [
                DatatypeBind () mb
            ] (Var () match)

datatypeDead :: Term TyName Name ()
datatypeDead = removeDeadBindings $
    let unitVal = embedIntoIR Unit.unitval
    in
        Let ()
            NonRec
            [
                DatatypeBind () maybeDatatype
            ] unitVal

singleBinding :: Term TyName Name ()
singleBinding = runQuote $ removeDeadBindings <$> do
    u <- freshTyName () "unit"
    uv <- freshName () "unitval"
    let unitVal = embedIntoIR Unit.unitval
    pure $ Let () NonRec [
        TypeBind () (TyVarDecl () u (PLC.Type ())) Unit.unit,
        TermBind () (VarDecl () uv Unit.unit) unitVal
        ] (Var () uv)

nestedBindings :: Term TyName Name ()
nestedBindings = runQuote $ removeDeadBindings <$> do
    u <- freshTyName () "unit"
    uv <- freshName () "unitval"
    let unitVal = embedIntoIR Unit.unitval
    pure $
        Let () NonRec [
        TypeBind () (TyVarDecl () u (PLC.Type ())) Unit.unit
        ] $
        Let () NonRec [
        TermBind () (VarDecl () uv Unit.unit) unitVal
        ] (Var () uv)

nestedBindingsIndirect :: Term TyName Name ()
nestedBindingsIndirect = runQuote $ removeDeadBindings <$> do
    u <- freshTyName () "unit"

    dt <- freshTyName () "SomeType"
    match <- freshName () "match_SomeType"
    constr <- freshName () "Constr"

    arg <- freshName () "arg"
    pure $
        Let () NonRec [
        -- only used by the constructor of dt, needs to not be removed
        TypeBind () (TyVarDecl () u (PLC.Type ())) Unit.unit
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

recBindingSimple :: Term TyName Name ()
recBindingSimple = runQuote $ removeDeadBindings <$> do
    uv <- freshName () "unitval"
    let unitVal = embedIntoIR Unit.unitval
    pure $ Let () Rec [
        TermBind () (VarDecl () uv Unit.unit) unitVal
        ] unitVal

recBindingComplex :: Term TyName Name ()
recBindingComplex = runQuote $ removeDeadBindings <$> do
    u <- freshTyName () "unit"
    uv <- freshName () "unitval"
    let unitVal = embedIntoIR Unit.unitval
    pure $ Let () Rec [
        TypeBind () (TyVarDecl () u (PLC.Type ())) Unit.unit,
        TermBind () (VarDecl () uv Unit.unit) unitVal
        ] (Var () uv)
