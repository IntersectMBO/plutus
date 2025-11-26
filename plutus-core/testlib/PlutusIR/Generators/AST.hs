-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}

{-| This module defines generators for PIR syntax trees for testing purposes.
It should only contain those generators that can't be reused from PLC
(PIR-exclusive constructs, Term, and Program) -}
module PlutusIR.Generators.AST
  ( module Export
  , regenConstantsUntil
  , genProgram
  , genTerm
  , genBinding
  , genDatatype
  , genTyVarDecl
  , genVarDecl
  , genRecursivity
  ) where

import PlutusIR
import PlutusIR.Subst

import PlutusCore.Default qualified as PLC
import PlutusCore.Generators.Hedgehog.AST as Export
  ( AstGen
  , genBuiltin
  , genConstant
  , genKind
  , genVersion
  , runAstGen
  , simpleRecursive
  )
import PlutusCore.Generators.Hedgehog.AST qualified as PLC

import Hedgehog hiding (Rec, Var)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Universe

regenConstantsUntil
  :: MonadGen m
  => (Some (ValueOf PLC.DefaultUni) -> Bool)
  -> Program tyname name PLC.DefaultUni fun ann
  -> m (Program tyname name PLC.DefaultUni fun ann)
regenConstantsUntil p =
  progTerm . termSubstConstantsM $ \ann -> fmap (fmap $ Constant ann) . PLC.regenConstantUntil p

genName :: PLC.AstGen Name
genName = Gen.filterT (not . isPirKw . _nameText) PLC.genName
  where
    isPirKw name =
      name
        `elem` [ "vardecl"
               , "typedecl"
               , "let"
               , "nonrec"
               , "rec"
               , "termbind"
               , "typebind"
               , "datatypebind"
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
  where
    listOf = Gen.list (Range.linear 0 10)

genBinding :: PLC.AstGen (Binding TyName Name PLC.DefaultUni PLC.DefaultFun ())
genBinding = Gen.choice [genTermBind, genTypeBind, genDatatypeBind]
  where
    genTermBind = TermBind () <$> genStrictness <*> genVarDecl <*> genTerm
    genTypeBind = TypeBind () <$> genTyVarDecl <*> genType
    genDatatypeBind = DatatypeBind () <$> genDatatype

genType :: PLC.AstGen (Type TyName PLC.DefaultUni ())
genType = simpleRecursive nonRecursive recursive
  where
    varGen = TyVar () <$> genTyName
    funGen = TyFun () <$> genType <*> genType
    lamGen = TyLam () <$> genTyName <*> genKind <*> genType
    forallGen = TyForall () <$> genTyName <*> genKind <*> genType
    applyGen = TyApp () <$> genType <*> genType
    sopGen = TySOP () <$> (Gen.list (Range.linear 0 10) (Gen.list (Range.linear 0 10) genType))
    recursive = [funGen, applyGen, sopGen]
    nonRecursive = [varGen, lamGen, forallGen]

genTerm :: PLC.AstGen (Term TyName Name PLC.DefaultUni PLC.DefaultFun ())
genTerm = simpleRecursive nonRecursive recursive
  where
    varGen = Var () <$> genName
    absGen = TyAbs () <$> genTyName <*> genKind <*> genTerm
    instGen = TyInst () <$> genTerm <*> genType
    lamGen = LamAbs () <$> genName <*> genType <*> genTerm
    applyGen = Apply () <$> genTerm <*> genTerm
    unwrapGen = Unwrap () <$> genTerm
    wrapGen = IWrap () <$> genType <*> genType <*> genTerm
    constrGen = Constr () <$> genType <*> Gen.word64 (Range.linear 0 10) <*> Gen.list (Range.linear 0 10) genTerm
    caseGen = Case () <$> genType <*> genTerm <*> Gen.list (Range.linear 0 10) genTerm
    errorGen = Error () <$> genType
    letGen = Let () <$> genRecursivity <*> Gen.nonEmpty (Range.linear 1 10) genBinding <*> genTerm
    recursive = [absGen, instGen, lamGen, applyGen, unwrapGen, wrapGen, letGen, constrGen, caseGen]
    nonRecursive = [varGen, Constant () <$> genConstant, Builtin () <$> genBuiltin, errorGen]

genProgram :: PLC.AstGen (Program TyName Name PLC.DefaultUni PLC.DefaultFun ())
genProgram = Program () <$> genVersion <*> genTerm
