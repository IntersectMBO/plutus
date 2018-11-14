module Generators ( genProgram
                  , emptyPosn
                  ) where

import qualified Data.ByteString.Lazy as BSL
import           Hedgehog             hiding (Size, Var)
import qualified Hedgehog.Gen         as Gen
import qualified Hedgehog.Range       as Range
import           Language.PlutusCore

genVersion :: MonadGen m => m (Version AlexPosn)
genVersion = Version emptyPosn <$> int' <*> int' <*> int'
    where int' = Gen.integral_ (Range.linear 0 10)

genTyName :: MonadGen m => m (TyName AlexPosn)
genTyName = TyName <$> genName

-- TODO make this robust against generating identfiers such as "fix"?
genName :: MonadGen m => m (Name AlexPosn)
genName = Name emptyPosn <$> name' <*> int'
    where int' = Unique <$> Gen.int (Range.linear 0 3000)
          name' = BSL.fromStrict <$> Gen.utf8 (Range.linear 1 20) Gen.lower

simpleRecursive :: MonadGen m => [m a] -> [m a] -> m a
simpleRecursive = Gen.recursive Gen.choice

genKind :: MonadGen m => m (Kind AlexPosn)
genKind = simpleRecursive nonRecursive recursive
    where nonRecursive = pure <$> sequence [Type, Size] emptyPosn
          recursive = [KindArrow emptyPosn <$> genKind <*> genKind]

genBuiltinName :: MonadGen m => m BuiltinName
genBuiltinName = Gen.element allBuiltinNames

genBuiltin :: MonadGen m => m (Builtin AlexPosn)
genBuiltin = BuiltinName emptyPosn <$> genBuiltinName

genConstant :: MonadGen m => m (Constant AlexPosn)
genConstant = Gen.choice [genInt, genSize, genBS]
    where int' = Gen.integral_ (Range.linear (-10000000) 10000000)
          size' = Gen.integral_ (Range.linear 1 10)
          string' = BSL.fromStrict <$> Gen.utf8 (Range.linear 0 40) Gen.unicode
          genInt = BuiltinInt emptyPosn <$> size' <*> int'
          genSize = BuiltinSize emptyPosn <$> size'
          genBS = BuiltinBS emptyPosn <$> size' <*> string'

genType :: MonadGen m => m (Type TyName AlexPosn)
genType = simpleRecursive nonRecursive recursive
    where varGen = TyVar emptyPosn <$> genTyName
          funGen = TyFun emptyPosn <$> genType <*> genType
          lamGen = TyLam emptyPosn <$> genTyName <*> genKind <*> genType
          forallGen = TyForall emptyPosn <$> genTyName <*> genKind <*> genType
          applyGen = TyApp emptyPosn <$> genType <*> genType
          numGen = TyInt emptyPosn <$> Gen.integral (Range.linear 0 256)
          recursive = [funGen, applyGen]
          nonRecursive = [varGen, lamGen, forallGen, numGen]

genTerm :: MonadGen m => m (Term TyName Name AlexPosn)
genTerm = simpleRecursive nonRecursive recursive
    where varGen = Var emptyPosn <$> genName
          absGen = TyAbs emptyPosn <$> genTyName <*> genKind <*> genTerm
          instGen = TyInst emptyPosn <$> genTerm <*> genType
          lamGen = LamAbs emptyPosn <$> genName <*> genType <*> genTerm
          applyGen = Apply emptyPosn <$> genTerm <*> genTerm
          unwrapGen = Unwrap emptyPosn <$> genTerm
          wrapGen = IWrap emptyPosn <$> genType <*> genType <*> genTerm
          errorGen = Error emptyPosn <$> genType
          recursive = [absGen, instGen, lamGen, applyGen, unwrapGen, wrapGen]
          nonRecursive = [varGen, Constant emptyPosn <$> genConstant, Builtin emptyPosn <$> genBuiltin, errorGen]

genProgram :: MonadGen m => m (Program TyName Name AlexPosn)
genProgram = Program emptyPosn <$> genVersion <*> genTerm

emptyPosn :: AlexPosn
emptyPosn = AlexPn 0 0 0
