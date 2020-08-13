-- | This module defines generators for PIR syntax trees for testing purposes.
-- It should only contain those generators that can't be reused from PLC
-- (PIR-exclusive constructs, Term, and Program)
{-# LANGUAGE OverloadedStrings #-}
module Language.PlutusIR.Generators.AST
    ( module Export
    , genProgram
    , genTerm
    , genBinding
    , genDatatype
    , genTyVarDecl
    , genVarDecl
    , genRecursivity
    ) where

import           Language.PlutusIR

import           Language.PlutusCore.Generators.AST as Export (AstGen, genBuiltinName, genConstant, genKind,
                                                               genStaticBuiltinName, genVersion, runAstGen,
                                                               simpleRecursive)
import qualified Language.PlutusCore.Generators.AST as PLC
import qualified Language.PlutusCore.Universe       as PLC

import           Hedgehog                           hiding (Var)
import qualified Hedgehog.Gen                       as Gen
import qualified Hedgehog.Internal.Gen              as Gen
import qualified Hedgehog.Range                     as Range

genName :: PLC.AstGen Name
genName = Gen.filterT (not . isPirKw . nameString) PLC.genName where
    isPirKw name = name `elem`
        [ "vardecl", "typedecl"
        , "let"
        , "nonrec", "rec"
        , "termbind", "typebind", "datatypebind"
        , "datatype"
        ]

genTyName :: PLC.AstGen TyName
genTyName = TyName <$> genName

genRecursivity :: MonadGen m => m Recursivity
genRecursivity = Gen.element [Rec, NonRec]

genStrictness :: MonadGen m => m Strictness
genStrictness = Gen.element [Strict, NonStrict]

genVarDecl :: PLC.AstGen (VarDecl TyName Name PLC.DefaultUni ())
genVarDecl = VarDecl () <$> genName <*> genType

genTyVarDecl :: PLC.AstGen (TyVarDecl TyName ())
genTyVarDecl = TyVarDecl () <$> genTyName <*> genKind

genDatatype :: PLC.AstGen (Datatype TyName Name PLC.DefaultUni ())
genDatatype = Datatype () <$> genTyVarDecl <*> listOf genTyVarDecl <*> genName <*> listOf genVarDecl
    where listOf = Gen.list (Range.linear 0 10)

genBinding :: PLC.AstGen (Binding TyName Name PLC.DefaultUni ())
genBinding = Gen.choice [genTermBind, genTypeBind, genDatatypeBind] where
    genTermBind = TermBind () <$> genStrictness <*> genVarDecl <*> genTerm
    genTypeBind = TypeBind () <$> genTyVarDecl <*> genType
    genDatatypeBind = DatatypeBind () <$> genDatatype

genType :: PLC.AstGen (Type TyName PLC.DefaultUni ())
genType = simpleRecursive nonRecursive recursive where
    varGen = TyVar () <$> genTyName
    funGen = TyFun () <$> genType <*> genType
    lamGen = TyLam () <$> genTyName <*> genKind <*> genType
    forallGen = TyForall () <$> genTyName <*> genKind <*> genType
    applyGen = TyApp () <$> genType <*> genType
    recursive = [funGen, applyGen]
    nonRecursive = [varGen, lamGen, forallGen]

genTerm :: PLC.AstGen (Term TyName Name PLC.DefaultUni ())
genTerm = simpleRecursive nonRecursive recursive where
    varGen = Var () <$> genName
    absGen = TyAbs () <$> genTyName <*> genKind <*> genTerm
    instGen = TyInst () <$> genTerm <*> genType
    lamGen = LamAbs () <$> genName <*> genType <*> genTerm
    applyGen = Apply () <$> genTerm <*> genTerm
    unwrapGen = Unwrap () <$> genTerm
    wrapGen = IWrap () <$> genType <*> genType <*> genTerm
    errorGen = Error () <$> genType
    letGen = Let () <$> genRecursivity <*> Gen.nonEmpty (Range.linear 1 10) genBinding <*> genTerm
    recursive = [absGen, instGen, lamGen, applyGen, unwrapGen, wrapGen, letGen]
    nonRecursive = [varGen, Constant () <$> genConstant, Builtin () <$> genBuiltinName, errorGen]

genProgram :: PLC.AstGen (Program TyName Name PLC.DefaultUni ())
genProgram = Program () <$> genTerm
