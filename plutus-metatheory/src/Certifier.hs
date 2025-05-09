module Certifier (runCertifier) where

import Control.Monad ((>=>))
import Data.List (find)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Maybe (fromJust)
import Data.Time.Clock.System (getSystemTime, systemNanoseconds)
import System.Directory (createDirectory)

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
  let cert = mkAgdaCertificateProject $ mkCertificate certName rawAgdaTrace
  writeCertificateProject cert
runCertifier Nothing _ = pure ()

type EquivClass = Int

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
  , certReprAsts :: [Ast]
  }

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

    getRepresentatives :: [NonEmpty Ast] -> [Ast]
    getRepresentatives = fmap NE.head

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

mkAgdaOpenImport :: String -> String
mkAgdaOpenImport agdaModuleName =
  "open import " <> agdaModuleName

newtype AgdaVar = AgdaVar String

instance AgdaUnparse AgdaVar where
  agdaUnparse (AgdaVar var) = var

mkCertificateFile :: Certificate -> (FilePath, String)
mkCertificateFile Certificate { certName, certTrace, certReprAsts } =
  let imports = fmap (mkAgdaOpenImport . mkAstModuleName) certReprAsts
      agdaTrace =
        agdaUnparse
        $ (\(st, (ast1, ast2)) ->
            (st
            , (AgdaVar $ "ast" <> (show . equivClass) ast1
              , AgdaVar $ "ast" <> (show . equivClass) ast2
              )
            )
          )
        <$> certTrace
      certFile = certName <> ".agda"
   in (certFile, mkCertificateModule certName agdaTrace imports)

mkCertificateModule :: String -> String -> [String] -> String
mkCertificateModule certModule agdaTrace imports =
  "module " <> certModule <> " where\
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
  \\n" <> unlines imports <> "\n" <>
  "\n\
  \\nasts : List (SimplifierTag × Untyped × Untyped)\
  \\nasts = " <> agdaTrace <>
  "\n\
  \\ncertificate : passed? (runCertifier asts) ≡ true\
  \\ncertificate = refl\
  \\n"

data AgdaCertificateProject = AgdaCertificateProject
  { mainModule :: (FilePath, String)
  , astModules :: [(FilePath, String)]
  , projectDir :: FilePath
  , agdalib    :: (FilePath, String)
  }

mkAgdaLib :: String -> (FilePath, String)
mkAgdaLib name =
  let contents =
        "name: " <> name <>
        "\ndepend:\
        \\n  standard-library-2.1.1\
        \\n  plutus-metatheory\
        \\ninclude: src"
   in (name <> ".agda-lib", contents)

mkAgdaCertificateProject
  :: Certificate
  -> AgdaCertificateProject
mkAgdaCertificateProject cert =
  let name = certName cert
      mainModule = mkCertificateFile cert
      astModules = fmap mkAgdaAstFile (certReprAsts cert)
      projectDir = name
      agdalib = mkAgdaLib name
   in AgdaCertificateProject { mainModule, astModules, projectDir, agdalib }

writeCertificateProject
  :: AgdaCertificateProject
  -> IO ()
writeCertificateProject AgdaCertificateProject { mainModule, astModules, projectDir, agdalib } = do
  let (mainModulePath, mainModuleContents) = mainModule
      (agdalibPath, agdalibContents) = agdalib
      astModulePaths = fmap fst astModules
      astModuleContents = fmap snd astModules
  time <- systemNanoseconds <$> getSystemTime
  let actualProjectDir = projectDir <> "-" <> show time
  createDirectory actualProjectDir
  createDirectory (actualProjectDir <> "/src")
  writeFile (actualProjectDir <> "/src/" <> mainModulePath) mainModuleContents
  writeFile (actualProjectDir <> "/" <> agdalibPath) agdalibContents
  mapM_ (\(path, contents) -> writeFile (actualProjectDir <> "/src/" <> path) contents) astModules
  putStrLn $ "Agda certificate project written to " <> actualProjectDir
