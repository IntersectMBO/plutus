{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall #-}

module Certifier
  ( runCertifier
  , mkCertifier
  , prettyCertifierError
  , CertName
  , CertifierError (..)
  , CertifierOutput (..)
  ) where

import Control.Monad
import Control.Monad.Except (ExceptT (..), runExceptT, throwError)
import Control.Monad.IO.Class (liftIO)
import Data.FileEmbed (embedStringFile)
import Data.Foldable
import Data.List.Extra (replace)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.List.NonEmptySep as NES
import Data.Text qualified as Text
import Data.Text.IO qualified as T
import System.Directory (createDirectoryIfMissing)
import System.FilePath (takeBaseName, (</>))
import Text.Printf (printf)

import FFI.AgdaUnparse (AgdaUnparse (..), renderAgdaUnparse)
import FFI.CostInfo
import FFI.OptimizerTrace
import FFI.Untyped (UTerm)
import MAlonzo.Code.Certifier (runCertifierMain)
import PlutusLedgerApi.Common
import Prettyprinter (pretty)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek
import UntypedPlutusCore.Transform.Certify.Hints (Hints)
import UntypedPlutusCore.Transform.Optimizer

type CertName = String
type CertDir = FilePath

data CertifierError
  = -- | Certificate dir + certifier report
    InvalidCertificate CertDir String
  | InvalidCompilerOutput
  | ValidationError CertName

data CertifierOutput
  = -- | Print minimal basic info, such as "passed" or "failed"
    BasicOutput
  | -- | Produce a detailed human readable report
    ReportOutput FilePath
  | -- | Produce an Agda project that can be type checked
    ProjectOutput CertDir

prettyCertifierError :: CertifierError -> String
prettyCertifierError (InvalidCertificate certDir report) =
  "\n\nInvalid certificate: "
    <> certDir
    <> "\nThe compilation was not successfully certified. \
       \Please open a bug report at https://www.github.com/IntersectMBO/plutus \
       \and attach the faulty certificate.\n\
       \Certifier report:\n"
    <> report
    <> "\n"
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

type Certifier = ExceptT CertifierError IO

runCertifier :: Certifier a -> IO (Either CertifierError a)
runCertifier = runExceptT

-- | Run the Agda certifier on the simplification trace, if requested
mkCertifier
  :: OptimizerTrace UPLC.Name UPLC.DefaultUni UPLC.DefaultFun a
  -- ^ The trace produced by the simplification process
  -> CertName
  -- ^ The name of the certificate to be produced
  -> CertifierOutput
  -> [ ( Maybe
           (CekEvaluationException UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun)
       , ExBudget
       )
     ]
  -> Certifier Bool
mkCertifier simplTrace certName certOutput costs = do
  let rawAgdaTrace = mkFfiOptimizerTrace simplTrace
      costs' :: [EvalResult]
      costs' = uncurry toEvalResult <$> reverse costs
  case runCertifierMain rawAgdaTrace costs' of
    Just (passed, report) -> do
      case certOutput of
        BasicOutput -> pure ()
        ReportOutput file -> liftIO $ T.writeFile file report
        ProjectOutput certDir -> do
          let cert = mkAgdaCertificateProject $ mkCertificate certName rawAgdaTrace
          writeCertificateProject certDir cert
          unless passed . throwError $ InvalidCertificate certDir (Text.unpack report)
      pure passed
    Nothing -> throwError InvalidCompilerOutput

data Certificate = Certificate
  { certName :: String
  , certTrace :: Trace UTerm
  }

mkCertificate :: String -> Trace UTerm -> Certificate
mkCertificate certName rawTrace =
  let trace' = dedup rawTrace
   in Certificate
        { certName
        , certTrace = trace'
        }
  where
    dedup :: Trace UTerm -> Trace UTerm
    dedup (Singleton x) = Singleton x
    dedup (Cons x sep xs)
      -- If subsequent ASTs are equal, drop the pass
      | x == NES.head xs = dedup xs
      | otherwise = Cons x sep (dedup xs)

{-| Module name with string components, e.g.
  "Data" :| ["List", "NonEmpty"] -}
type ModuleName = NonEmpty String

moduleIdent :: ModuleName -> String
moduleIdent = fold . NE.intersperse "."

moduleFileName :: ModuleName -> FilePath
moduleFileName m = foldr (</>) "" m ++ ".agda"

-- | Drops the last component of the module to obtain its directory
moduleDir :: ModuleName -> String
moduleDir m = foldr (</>) "" (NE.init m)

{-| Module name in agda, for a given equivalence class. Each list element is a module segment that is to be
separated by "." (agda identifier) or by "/" (files) -}
mkAstModuleName :: Int -> ModuleName
mkAstModuleName n =
  ("Pass" <> printf "%03d" n) :| ["AST"]

mkAgdaAstFile :: Int -> UTerm -> Maybe Hints -> (ModuleName, String)
mkAgdaAstFile n pre mHints =
  ( modName
  , unlines $
      [ "module " <> moduleIdent modName <> " where"
      , ""
      , "open import Data.Unit"
      , "open import Data.Nat"
      , "open import Data.Integer"
      , "open import Data.Maybe"
      , "open import Data.Bool.Base using (Bool; false; true)"
      , "open import Data.List using (List; _∷_; [])"
      , ""
      , "open import RawU"
      , "open import Builtin"
      , "open import Utils"
      , ""
      , "open import Untyped using (_⊢)"
      , "open import VerifiedCompilation using (checkScope)"
      , "open import VerifiedCompilation.Trace"
      , ""
      , "raw : Untyped"
      , "raw = " <> renderAgdaUnparse pre
      , ""
      , "ast : 0 ⊢"
      , "ast = to-witness-T (checkScope raw) tt"
      ]
        ++ case mHints of
          Just hints ->
            [ ""
            , "hints : Hints"
            , "hints = " <> renderAgdaUnparse hints
            ]
          Nothing -> []
  )
  where
    modName = mkAstModuleName n

mkAgdaImport :: Bool -> ModuleName -> String
mkAgdaImport open moduleName =
  openModifier open ("import " <> moduleIdent moduleName)
  where
    openModifier True str = "open " <> str
    openModifier False str = str

newtype AgdaVar = AgdaVar String

instance AgdaUnparse AgdaVar where
  agdaUnparse (AgdaVar var) = pretty var

mkCertificateFile :: Certificate -> String
mkCertificateFile Certificate {certName, certTrace} =
  unlines $
    [ "module " <> certName <> " where"
    , ""
    , "open import VerifiedCompilation.Trace"
    , "open import Untyped using (_⊢)"
    , "open import Utils hiding (List; _>>=_)"
    , "open import VerifiedCompilation"
    , "open import Data.Unit"
    , ""
    ]
      ++ map (mkAgdaImport False) astImports
      ++ [ ""
         , "trace : Trace (0 ⊢)"
         , "trace ="
         ]
      ++ map ("  " ++) (printTrace traceExpr)
      ++ [ ""
         , "certificate : Certificate trace"
         , "certificate = cert trace (certify trace) tt"
         , ""
         ]
  where
    astImports :: [ModuleName]
    astImports = map mkAstModuleName [0 .. length certTrace - 1]

    -- replace hints and asts by agda variables that point to the right module
    traceExpr :: NonEmptySep (OptStage, AgdaVar) AgdaVar
    traceExpr = go 0 certTrace
      where
        go n (Singleton _) = Singleton (moduleVar n "ast")
        go n (Cons _ (stage, _) xs) =
          Cons
            (moduleVar n "ast")
            (stage, moduleVar n "hints")
            (go (n + 1) xs)

    moduleVar :: Int -> String -> AgdaVar
    moduleVar n x =
      AgdaVar $
        moduleIdent (mkAstModuleName n)
          <> "."
          <> x

-- Ad-hoc pretty printing so it can be printed over multiple lines
printTrace :: NonEmptySep (OptStage, AgdaVar) AgdaVar -> [String]
printTrace (Singleton x) = ["singleton" ++ " " ++ renderAgdaUnparse x]
printTrace (Cons x (stage, y) xs) =
  [ renderAgdaUnparse x
  , "  ∷[ " ++ renderAgdaUnparse stage ++ " , " ++ renderAgdaUnparse y ++ " ]"
  ]
    ++ printTrace xs

data AgdaCertificateProject = AgdaCertificateProject
  { mainModule :: (FilePath, String)
  , astModules :: [(ModuleName, String)]
  , agdalib :: (FilePath, String)
  }

mkAgdaLib :: String -> (FilePath, String)
mkAgdaLib name =
  let contents =
        "name: "
          <> name
          <> "\ndepend:\
             \\n  standard-library-2.3\
             \\n  plutus-metatheory\
             \\ninclude: src\
             \\nflags: --polarity"
   in (name <> ".agda-lib", contents)

mkAgdaCertificateProject
  :: Certificate
  -> AgdaCertificateProject
mkAgdaCertificateProject cert =
  let name = certName cert
      mainModule = mkCertificateFile cert
      astModules = astModuleFiles 0 (certTrace cert)
      agdalib = mkAgdaLib name
   in AgdaCertificateProject
        { mainModule = (certName cert <> ".agda", mainModule)
        , astModules
        , agdalib
        }
  where
    astModuleFiles :: Int -> Trace UTerm -> [(ModuleName, String)]
    astModuleFiles n (Singleton x) = [mkAgdaAstFile n x Nothing]
    astModuleFiles n (Cons x (_, h) xs) = mkAgdaAstFile n x (Just h) : astModuleFiles (n + 1) xs

writeCertificateProject
  :: CertDir
  -> AgdaCertificateProject
  -> Certifier ()
writeCertificateProject
  certDir
  AgdaCertificateProject
    { mainModule
    , astModules
    , agdalib
    } =
    liftIO $ do
      let (mainModulePath, mainModuleContents) = mainModule
          (agdalibPath, agdalibContents) = agdalib
          certName = takeBaseName mainModulePath
      createDirectoryIfMissing True certDir
      createDirectoryIfMissing True (certDir </> "src")
      for_ astModules $ \(modName, _) -> do
        createDirectoryIfMissing True (certDir </> "src" </> moduleDir modName)
      writeFile (certDir </> "src" </> mainModulePath) mainModuleContents
      writeFile (certDir </> agdalibPath) agdalibContents
      let readmeTemplate = $(embedStringFile "file-embed/certificate-README.md")
      writeFile (certDir </> "README.md") (replace "{{NAME}}" certName readmeTemplate)
      traverse_
        ( \(modName, contents) ->
            writeFile (certDir </> "src" </> moduleFileName modName) contents
        )
        astModules
