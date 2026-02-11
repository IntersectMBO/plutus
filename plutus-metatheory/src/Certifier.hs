{-# OPTIONS_GHC -Wall #-}

module Certifier
  ( runCertifier
  , mkCertifier
  , prettyCertifierError
  , prettyCertifierSuccess
  , CertifierError (..)
  ) where

import Control.Monad.Except (ExceptT (..), runExceptT, throwError)
import Control.Monad.IO.Class (liftIO)
import Data.Char (toUpper)
import Data.List (find)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Maybe (fromMaybe)
import Data.Time.Clock.System (getSystemTime, systemNanoseconds)
import System.Directory (createDirectory)
import System.FilePath ((</>))

import FFI.AgdaUnparse (AgdaUnparse (..))
import FFI.SimplifierTrace (Trace, mkFfiSimplifierTrace)
import FFI.Untyped (UTerm)

import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Transform.Simplifier

import MAlonzo.Code.VerifiedCompilation (runCertifierMain)

type CertName = String
type CertDir = String

data CertifierError
  = InvalidCertificate CertDir
  | InvalidCompilerOutput
  | ValidationError CertName

newtype CertifierSuccess = CertifierSuccess CertDir

prettyCertifierError :: CertifierError -> String
prettyCertifierError (InvalidCertificate certDir) =
  "\n\nInvalid certificate: "
    <> certDir
    <> "\nThe compilation was not successfully certified. \
       \Please open a bug report at https://www.github.com/IntersectMBO/plutus \
       \and attach the faulty certificate.\n"
prettyCertifierError InvalidCompilerOutput =
  "\n\nInvalid compiler output: \
  \\nThe certifier was not able to process the trace produced by the compiler. \
  \Please open a bug report at https://www.github.com/IntersectMBO/plutus \
  \containing a minimal program that when compiled reproduces the issue.\n"
prettyCertifierError (ValidationError name) =
  "\n\nInvalid certificate name: \
  \\nThe certificate name "
    <> name
    <> " is invalid. \
       \Please use only alphanumeric characters, underscores and dashes. \
       \The first character must be a letter.\n"

prettyCertifierSuccess :: CertifierSuccess -> String
prettyCertifierSuccess (CertifierSuccess certDir) =
  "\n\nCertificate successfully created: "
    <> certDir
    <> "\nThe compilation was successfully certified.\n"

type Certifier = ExceptT CertifierError IO

runCertifier :: Certifier a -> IO (Either CertifierError a)
runCertifier = runExceptT

-- | Run the Agda certifier on the simplification trace, if requested
mkCertifier
  :: SimplifierTrace UPLC.Name UPLC.DefaultUni UPLC.DefaultFun a
  -- ^ The trace produced by the simplification process
  -> CertName
  -- ^ The name of the certificate to be produced
  -> Certifier CertifierSuccess
mkCertifier simplTrace certName = do
  certName' <- validCertName certName
  let rawAgdaTrace = mkFfiSimplifierTrace simplTrace
  case runCertifierMain rawAgdaTrace of
    Just True -> do
      let cert = mkAgdaCertificateProject $ mkCertificate certName' rawAgdaTrace
      CertifierSuccess <$> writeCertificateProject cert
    Just False -> do
      let cert = mkAgdaCertificateProject $ mkCertificate certName' rawAgdaTrace
      certDir <- writeCertificateProject cert
      throwError $ InvalidCertificate certDir
    Nothing -> throwError InvalidCompilerOutput

validCertName :: String -> Certifier String
validCertName [] = throwError $ ValidationError []
validCertName name@(fstC : rest) =
  if all isValidChar name
    then pure (toUpper fstC : rest)
    else throwError $ ValidationError name
  where
    isValidChar c = c `elem` ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9'] ++ "_-"

type EquivClass = Int

data TermWithId = TermWithId
  { termId :: Int
  , term :: UTerm
  }

data Ast = Ast
  { equivClass :: EquivClass
  , astTermWithId :: TermWithId
  }

getTermId :: Ast -> Int
getTermId Ast {astTermWithId = TermWithId {termId}} = termId

data Certificate = Certificate
  { certName :: String
  , certTrace :: Trace Ast
  , certReprAsts :: [Ast]
  }

mkCertificate :: String -> Trace UTerm -> Certificate
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
      :: Trace UTerm
      -> Trace TermWithId
    addIds = go 0
      where
        go
          :: Int
          -> Trace UTerm
          -> Trace TermWithId
        go _ [] = []
        go id' ((stage, (hints, (before, after))) : rest) =
          let beforeWithId = TermWithId id' before
              afterWithId = TermWithId (id' + 1) after
           in (stage, (hints, (beforeWithId, afterWithId))) : go (id' + 2) rest

    extractTermWithIds
      :: Trace TermWithId
      -> [TermWithId]
    extractTermWithIds = concatMap (\(_, (_, (before, after))) -> [before, after])

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

    errorMessage :: String
    errorMessage =
      "Internal error: could not find AST.\
      \ This is an issue in the certifier, please open a bug report at\
      \ https://github.com/IntersectMBO/plutus/issues"

    mkAstTrace
      :: [Ast]
      -> Trace TermWithId
      -> Trace Ast
    mkAstTrace _ [] = []
    mkAstTrace allAsts ((stage, (hints, (rawBefore, rawAfter))) : rest) =
      let processedBefore =
            fromMaybe (error errorMessage) $
              find (\ast -> getTermId ast == termId rawBefore) allAsts
          processedAfter =
            fromMaybe (error errorMessage) $
              find (\ast -> getTermId ast == termId rawAfter) allAsts
       in (stage, (hints, (processedBefore, processedAfter))) : mkAstTrace allAsts rest

mkAstModuleName :: Ast -> String
mkAstModuleName Ast {equivClass} =
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
  "module "
    <> agdaIdStr
    <> " where\
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
       \\n"
    <> agdaAstTy
    <> "\n\
       \\n"
    <> agdaAstDef
    <> "\n"

mkAgdaOpenImport :: String -> String
mkAgdaOpenImport agdaModuleName =
  "open import " <> agdaModuleName

newtype AgdaVar = AgdaVar String

instance AgdaUnparse AgdaVar where
  agdaUnparse (AgdaVar var) = var

mkCertificateFile :: Certificate -> (FilePath, String)
mkCertificateFile Certificate {certName, certTrace, certReprAsts} =
  let imports = fmap (mkAgdaOpenImport . mkAstModuleName) certReprAsts
      agdaTrace =
        agdaUnparse $
          ( \(st, (hints, (ast1, ast2))) ->
              ( st
              ,
                ( hints
                ,
                  ( AgdaVar $ "ast" <> (show . equivClass) ast1
                  , AgdaVar $ "ast" <> (show . equivClass) ast2
                  )
                )
              )
          )
            <$> certTrace
      certFile = certName <> ".agda"
   in (certFile, mkCertificateModule certName agdaTrace imports)

mkCertificateModule :: String -> String -> [String] -> String
mkCertificateModule certModule agdaTrace imports =
  "module "
    <> certModule
    <> " where\
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
       \\n"
    <> unlines imports
    <> "\n"
    <> "\n\
       \\nasts : List (SimplifierTag × Hints × Untyped × Untyped)\
       \\nasts = "
    <> agdaTrace
    <> "\n\
       \\ncertificate : passed? (runCertifier asts) ≡ true\
       \\ncertificate = refl\
       \\n"

data AgdaCertificateProject = AgdaCertificateProject
  { mainModule :: (FilePath, String)
  , astModules :: [(FilePath, String)]
  , projectDir :: FilePath
  , agdalib :: (FilePath, String)
  }

mkAgdaLib :: String -> (FilePath, String)
mkAgdaLib name =
  let contents =
        "name: "
          <> name
          <> "\ndepend:\
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
   in AgdaCertificateProject {mainModule, astModules, projectDir, agdalib}

writeCertificateProject
  :: AgdaCertificateProject
  -> Certifier CertDir
writeCertificateProject
  AgdaCertificateProject
    { mainModule
    , astModules
    , projectDir
    , agdalib
    } =
    liftIO $ do
      let (mainModulePath, mainModuleContents) = mainModule
          (agdalibPath, agdalibContents) = agdalib
      time <- systemNanoseconds <$> getSystemTime
      let actualProjectDir = projectDir <> "-" <> show time
      createDirectory actualProjectDir
      createDirectory (actualProjectDir </> "src")
      writeFile (actualProjectDir </> "src" </> mainModulePath) mainModuleContents
      writeFile (actualProjectDir </> agdalibPath) agdalibContents
      mapM_
        ( \(path, contents) ->
            writeFile (actualProjectDir </> "src" </> path) contents
        )
        astModules
      pure actualProjectDir
