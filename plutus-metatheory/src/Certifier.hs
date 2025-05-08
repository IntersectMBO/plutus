module Certifier (runCertifier) where

import Control.Monad ((>=>))
import Data.List (find)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Maybe (fromJust)

import FFI.AgdaUnparse (agdaUnparse)
import FFI.SimplifierTrace (mkFfiSimplifierTrace)
import FFI.Untyped (UTerm)

import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Transform.Simplifier

import MAlonzo.Code.VerifiedCompilation (runCertifierMain)

-- | Run the Agda certifier on the simplification trace, if requested
runCertifier
  :: Maybe String
  -- ^ Should we run the Agda certifier? If so, what should the certificate file be called?
  -> SimplifierTrace UPLC.Name UPLC.DefaultUni UPLC.DefaultFun a
  -- ^ The trace produced by the simplification process
  -> IO ()
runCertifier (Just certName) simplTrace = do
  let rawAgdaTrace = mkFfiSimplifierTrace simplTrace
  case runCertifierMain rawAgdaTrace of
    Just True ->
      putStrLn "The compilation was successfully certified."
    Just False ->
      putStrLn
        "The compilation was not successfully certified. \
        \Please open a bug report at https://www.github.com/IntersectMBO/plutus \
        \and attach the faulty certificate."
    Nothing ->
      putStrLn
        "The certifier was unable to check the compilation. \
        \Please open a bug report at https://www.github.com/IntersectMBO/plutus."
  writeFile (certName ++ ".agda") (rawCertificate certName rawAgdaTrace)
runCertifier Nothing _ = pure ()

rawCertificate :: String -> [(SimplifierStage, (UTerm, UTerm))] -> String
rawCertificate certName rawTrace =
  "module " <> certName <> " where\
  \\n\
  \\nopen import VerifiedCompilation\
  \\nopen import VerifiedCompilation.Certificate\
  \\nopen import Untyped\
  \\nopen import RawU\
  \\nopen import Builtin\
  \\nopen import Data.Unit\
  \\nopen import Data.Nat\
  \\nopen import Data.Integer\
  \\nopen import Utils\
  \\nimport Agda.Builtin.Bool\
  \\nimport Relation.Nullary\
  \\nimport VerifiedCompilation.UntypedTranslation\
  \\nopen import Agda.Builtin.Maybe\
  \\nopen import Data.Empty using (⊥)\
  \\nopen import Data.Bool.Base using (Bool; false; true)\
  \\nopen import Agda.Builtin.Equality using (_≡_; refl)\
  \\n\
  \\nasts : List (SimplifierTag × Untyped × Untyped)\
  \\nasts = " <> agdaUnparse rawTrace <>
  "\n\
  \\ncertificate : passed? (runCertifier asts) ≡ true\
  \\ncertificate = refl\
  \\n"

type AstId = Int
type EquivClass = Int

data Ast = Ast
  { astId      :: AstId
  , equivClass :: Maybe EquivClass
  , astTerm    :: UTerm
  }

initAst :: AstId -> UTerm -> Ast
initAst astId term =
  Ast
    { astId = astId
    , equivClass = Nothing
    , astTerm = term
    }

unsafeEquivClass :: Ast -> EquivClass
unsafeEquivClass ast =
  case equivClass ast of
    Just cl -> cl
    Nothing -> error "EquivClass is missing."

mkAgdaTrace :: [(SimplifierStage, (UTerm, UTerm))] -> [(SimplifierStage, (EquivClass, EquivClass))]
mkAgdaTrace sTrace =
  let initTr = initAstTrace sTrace
      allRawAsts = initTr >>= (\(stage, (before, after)) -> [before, after])
      groupedAsts = findEquivClasses allRawAsts
      processedAsts = groupedAsts >>= NE.toList
      processedAstTrace = processAstTrace processedAsts initTr
   in fmap (\(st, (bf, af)) -> (st, (unsafeEquivClass bf, unsafeEquivClass af))) processedAstTrace

processAstTrace :: [Ast] -> [(SimplifierStage, (Ast, Ast))] -> [(SimplifierStage, (Ast, Ast))]
processAstTrace _ [] = []
processAstTrace allAsts ((stage, (rawBefore, rawAfter)) : rest) =
  let Just processedBefore = find (\ast -> astId ast == astId rawBefore) allAsts
      Just processedAfter = find (\ast -> astId ast == astId rawAfter) allAsts
   in (stage, (processedBefore, processedAfter)) : processAstTrace allAsts rest

initAstTrace :: [(SimplifierStage, (UTerm, UTerm))] -> [(SimplifierStage, (Ast, Ast))]
initAstTrace sTrace = go 0 sTrace
  where
    go :: AstId -> [(SimplifierStage, (UTerm, UTerm))] -> [(SimplifierStage, (Ast, Ast))]
    go _ [] = []
    go astId ((stage, (before, after)) : rest) =
      let beforeAst = initAst astId before
          afterAst = initAst (astId + 1) after
       in (stage, (beforeAst, afterAst)) : go (astId + 2) rest

findEquivClasses :: [Ast] -> [NonEmpty Ast]
findEquivClasses =
  go 0 . NE.groupBy (\x y -> astTerm x == astTerm y)
  where
    go :: EquivClass -> [NonEmpty Ast] -> [NonEmpty Ast]
    go _ [] = []
    go cl (asts : rest) =
      let asts' = fmap (\x -> x {equivClass = Just cl}) asts
       in asts' : go (cl + 1) rest

chooseRepresentatives :: [NonEmpty Ast] -> [Ast]
chooseRepresentatives = fmap NE.head

mkAgdaAstFiles :: [Ast] -> [(FilePath, String)]
mkAgdaAstFiles = fmap go
  where
    go ast =
      let agdaAst = agdaUnparse (astTerm ast)
          agdaId = fromJust . equivClass $ ast
          agdaIdStr = "ast" <> show agdaId
          agdaAstTy = agdaIdStr <> " : Untyped"
          agdaAstDef = agdaIdStr <> " = " <> agdaAst
          agdaAstFile = "Ast" <> show agdaId <> ".agda"
       in (agdaAstFile, mkAstModule agdaIdStr agdaAstTy agdaAstDef)

mkAstModule :: String -> String -> String -> String
mkAstModule agdaIdStr agdaAstTy agdaAstDef =
  "module " <> agdaIdStr <> " where\
  \\n\
  \\nopen import VerifiedCompilation\
  \\nopen import VerifiedCompilation.Certificate\
  \\nopen import Untyped\
  \\nopen import RawU\
  \\nopen import Builtin\
  \\nopen import Data.Unit\
  \\nopen import Data.Nat\
  \\nopen import Data.Integer\
  \\nopen import Utils\
  \\nimport Agda.Builtin.Bool\
  \\nimport Relation.Nullary\
  \\nimport VerifiedCompilation.UntypedTranslation\
  \\nopen import Agda.Builtin.Maybe\
  \\nopen import Data.Empty using (⊥)\
  \\nopen import Data.Bool.Base using (Bool; false; true)\
  \\nopen import Agda.Builtin.Equality using (_≡_; refl)\
  \\n\
  \\n" <> agdaAstTy <> "\n\
  \\n" <> agdaAstDef <> "\n"

