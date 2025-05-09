module Certifier (runCertifier) where

import Control.Monad ((>=>))
import Data.List (find)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Maybe (fromJust)

import FFI.AgdaUnparse (AgdaUnparse (..))
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

type EquivClass = Int

newtype Representatives a = Representatives [a]

data TermWithId = TermWithId
  { termId :: Int
  , term   :: UTerm
  }

data Ast = Ast
  { equivClass    :: EquivClass
  , astTermWithId :: TermWithId
  }

getTermId :: Ast -> Int
getTermId Ast {astTermWithId = TermWithId {termId} } = termId

data Certificate = Certificate
  { certName     :: String
  , certTrace    :: [(SimplifierStage, (Ast, Ast))]
  , certReprAsts :: Representatives Ast
  }

instance AgdaUnparse Ast where
  agdaUnparse Ast {equivClass} = "Ast" <> show equivClass



mkCertificate :: String -> [(SimplifierStage, (UTerm, UTerm))] -> Certificate
mkCertificate certName rawTrace =
  let traceWithIds = addIds rawTrace
      allTermWithIds = extractTermWithIds traceWithIds
      groupedAsts = findEquivClasses allTermWithIds
      allAsts = groupedAsts >>= NE.toList
      certTrace = mkAstTrace allAsts traceWithIds
      certReprAsts = getRepresentatives groupedAsts
   in Certificate
        { certName
        , certTrace
        , certReprAsts
        }
  where
    addIds
      :: [(SimplifierStage, (UTerm, UTerm))]
      -> [(SimplifierStage, (TermWithId, TermWithId))]
    addIds = go 0
      where
        go
          :: Int
          -> [(SimplifierStage, (UTerm, UTerm))]
          -> [(SimplifierStage, (TermWithId, TermWithId))]
        go _ [] = []
        go id ((stage, (before, after)) : rest) =
          let beforeWithId = TermWithId id before
              afterWithId = TermWithId (id + 1) after
           in (stage, (beforeWithId, afterWithId)) : go (id + 2) rest

    extractTermWithIds
      :: [(SimplifierStage, (TermWithId, TermWithId))]
      -> [TermWithId]
    extractTermWithIds = concatMap (\(_, (before, after)) -> [before, after])

    findEquivClasses :: [TermWithId] -> [NonEmpty Ast]
    findEquivClasses =
      go 0 . NE.groupBy (\x y -> term x == term y)
      where
        go :: EquivClass -> [NonEmpty TermWithId] -> [NonEmpty Ast]
        go _ [] = []
        go cl (ts : rest) =
          let asts = fmap (\t -> Ast {astTermWithId = t, equivClass = cl}) ts
           in asts : go (cl + 1) rest

    getRepresentatives :: [NonEmpty Ast] -> Representatives Ast
    getRepresentatives = Representatives . fmap NE.head

    mkAsts :: [TermWithId] -> [Ast]
    mkAsts = findEquivClasses >=> NE.toList

    mkAstTrace
      :: [Ast]
      -> [(SimplifierStage, (TermWithId, TermWithId))]
      -> [(SimplifierStage, (Ast, Ast))]
    mkAstTrace _ [] = []
    mkAstTrace allAsts ((stage, (rawBefore, rawAfter)) : rest) =
      let Just processedBefore = find (\ast -> getTermId ast == termId rawBefore) allAsts
          Just processedAfter = find (\ast -> getTermId ast == termId rawAfter) allAsts
       in (stage, (processedBefore, processedAfter)) : mkAstTrace allAsts rest

mkAstModuleName :: Ast -> String
mkAstModuleName Ast { equivClass } =
  "Ast" <> show equivClass

mkAgdaAstFile :: Ast -> (FilePath, String)
mkAgdaAstFile ast =
  let agdaAst = agdaUnparse (term . astTermWithId $ ast)
      agdaId = equivClass ast
      agdaModuleName = mkAstModuleName ast
      agdaIdStr = "ast" <> show agdaId
      agdaAstTy = agdaIdStr <> " : Untyped"
      agdaAstDef = agdaIdStr <> " = " <> agdaAst
      agdaAstFile = agdaModuleName <> ".agda"
   in (agdaAstFile, mkAstModule agdaModuleName agdaAstTy agdaAstDef)

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
