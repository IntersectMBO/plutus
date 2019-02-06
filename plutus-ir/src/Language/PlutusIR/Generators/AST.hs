-- | This module defines generators for PIR syntax trees for testing purposes.
-- It should only contain those generators that can't be reused from PLC
-- (PIR-exclusive constructs, Term, and Program)
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
                                                               genName, genTyName, genType, genVersion, simpleRecursive)

import           Hedgehog                           hiding (Var)
import qualified Hedgehog.Gen                       as Gen
import qualified Hedgehog.Range                     as Range

genRecursivity :: MonadGen m => m Recursivity
genRecursivity = Gen.element [Rec, NonRec]

genVarDecl :: MonadGen m => m (VarDecl TyName Name ())
genVarDecl = VarDecl () <$> genName <*> genType

genTyVarDecl :: MonadGen m => m (TyVarDecl TyName ())
genTyVarDecl = TyVarDecl () <$> genTyName <*> genKind

genDatatype :: MonadGen m => m (Datatype TyName Name ())
genDatatype = Datatype () <$> genTyVarDecl <*> listOf genTyVarDecl <*> genName <*> listOf genVarDecl
    where listOf = Gen.list (Range.linear 1 10)

genBinding :: MonadGen m => m (Binding TyName Name ())
genBinding = Gen.choice [genTermBind, genTypeBind, genDatatypeBind]
    where genTermBind = TermBind () <$> genVarDecl <*> genTerm
          genTypeBind = TypeBind () <$> genTyVarDecl <*> genType
          genDatatypeBind = DatatypeBind () <$> genDatatype

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
