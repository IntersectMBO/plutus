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

import           Language.PlutusCore.Generators.AST as Export (genBuiltin, genBuiltinName, genConstant, genKind,
                                                               genVersion, simpleRecursive)
import qualified Language.PlutusCore.Generators.AST as PLC

import           Hedgehog                           hiding (Var)
import qualified Hedgehog.Gen                       as Gen
import qualified Hedgehog.Range                     as Range

genName :: MonadGen m => m (Name ())
genName = Gen.filter (not . isPirKw . nameString) PLC.genName
    where isPirKw "vardecl"      = True
          isPirKw "typedecl"     = True
          isPirKw "let"          = True
          isPirKw "nonrec"       = True
          isPirKw "rec"          = True
          isPirKw "termbind"     = True
          isPirKw "typebind"     = True
          isPirKw "datatypebind" = True
          isPirKw "datatype"     = True
          isPirKw _              = False

genTyName :: MonadGen m => m (TyName ())
genTyName = TyName <$> genName

genRecursivity :: MonadGen m => m Recursivity
genRecursivity = Gen.element [Rec, NonRec]

genVarDecl :: MonadGen m => m (VarDecl TyName Name ())
genVarDecl = VarDecl () <$> genName <*> genType

genTyVarDecl :: MonadGen m => m (TyVarDecl TyName ())
genTyVarDecl = TyVarDecl () <$> genTyName <*> genKind

genDatatype :: MonadGen m => m (Datatype TyName Name ())
genDatatype = Datatype () <$> genTyVarDecl <*> listOf genTyVarDecl <*> genName <*> listOf genVarDecl
    where listOf = Gen.list (Range.linear 0 10)

genBinding :: MonadGen m => m (Binding TyName Name ())
genBinding = Gen.choice [genTermBind, genTypeBind, genDatatypeBind]
    where genTermBind = TermBind () <$> genVarDecl <*> genTerm
          genTypeBind = TypeBind () <$> genTyVarDecl <*> genType
          genDatatypeBind = DatatypeBind () <$> genDatatype

genType :: MonadGen m => m (Type TyName ())
genType = simpleRecursive nonRecursive recursive
    where varGen = TyVar () <$> genTyName
          funGen = TyFun () <$> genType <*> genType
          lamGen = TyLam () <$> genTyName <*> genKind <*> genType
          forallGen = TyForall () <$> genTyName <*> genKind <*> genType
          applyGen = TyApp () <$> genType <*> genType
          recursive = [funGen, applyGen]
          nonRecursive = [varGen, lamGen, forallGen]

genTerm :: MonadGen m => m (Term TyName Name ())
genTerm = simpleRecursive nonRecursive recursive
    where varGen = Var () <$> genName
          absGen = TyAbs () <$> genTyName <*> genKind <*> genTerm
          instGen = TyInst () <$> genTerm <*> genType
          lamGen = LamAbs () <$> genName <*> genType <*> genTerm
          applyGen = Apply () <$> genTerm <*> genTerm
          unwrapGen = Unwrap () <$> genTerm
          wrapGen = IWrap () <$> genType <*> genType <*> genTerm
          errorGen = Error () <$> genType
          letGen = Let () <$> genRecursivity <*> Gen.list (Range.linear 1 10) genBinding <*> genTerm
          recursive = [absGen, instGen, lamGen, applyGen, unwrapGen, wrapGen, letGen]
          nonRecursive = [varGen, Constant () <$> genConstant, Builtin () <$> genBuiltin, errorGen]

genProgram :: MonadGen m => m (Program TyName Name ())
genProgram = Program () <$> genTerm
