{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
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
import Data.List (intercalate)
import Data.List.Extra (replace)
import Data.List.NonEmpty (NonEmpty (..), cons)
import Data.List.NonEmpty qualified as NE
import Data.List.NonEmptySep as NES
import Data.String
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

-- | Convert module name to an Agda identifier
toIdent :: ModuleName -> String
toIdent = fold . NE.intersperse "."

-- | Convert module name to .agda filepath relative to the source directory
toFilePath :: ModuleName -> FilePath
toFilePath m = foldr (</>) "" m ++ ".agda"

-- | Drops the last component of the module to obtain its directory
moduleDir :: ModuleName -> String
moduleDir m = foldr (</>) "" (NE.init m)

enclose :: String -> String -> String -> String
enclose l r x = l ++ x ++ r

data ImportHow = Open | Closed

type Import = (ImportHow, ModuleName, [String])

renderImport :: Import -> String
renderImport (how, name, idents) =
  renderHow ++ "import " ++ toIdent name ++ renderUsing
  where
    renderHow = case how of
      Open -> "open "
      Closed -> ""
    renderUsing
      | null idents = ""
      | otherwise = " using (" ++ intercalate ", " idents ++ ")"

{-| Module name in agda, for a given ast number and module name. Each list element is a module segment that is to be
separated by "." (agda identifier) or by "/" (files) -}
passModName :: String -> Int -> ModuleName
passModName name n =
  ("Pass" <> printf "%03d" n) :| [name]

astModName :: Int -> ModuleName
astModName n = passModName "AST" n

proofModName :: Int -> ModuleName
proofModName n = passModName "Proof" n

proofFile :: Int -> UTerm -> Maybe (OptStage, Hints) -> (ModuleName, String)
proofFile n _ Nothing = (proofModName n, [])
proofFile n _ (Just (pass, _)) =
  ( modName
  , unlines $
      [ "module " <> toIdent modName <> " where"
      , ""
      ]
        ++ map renderImport imports
        ++ [ ""
           , "related : " ++ proofSig
           , "related = " ++ proofExpr
           ]
  )
  where
    modName = proofModName n

    preMod = astModName n
    postMod = astModName (n + 1)

    preTerm = toIdent preMod ++ ".ast"
    postTerm = toIdent postMod ++ ".ast"
    hints = toIdent preMod ++ ".hints"

    proofSig :: String
    proofSig =
      unwords
        ["RelationOf", renderAgdaUnparse pass, preTerm, postTerm]

    proofExpr :: String
    proofExpr =
      unwords
        [ "to-witness-T"
        , enclose "(" ")" . unwords $
            [ "certifyPass"
            , renderAgdaUnparse pass
            , hints
            , preTerm
            , postTerm
            ]
        , "tt"
        ]

    imports :: [(ImportHow, ModuleName, [String])]
    imports =
      [ (Closed, preMod, [])
      , (Closed, postMod, [])
      , (Open, "Data" :| ["Unit"], ["tt"])
      , (Open, "VerifiedCompilation" :| [], [])
      , (Open, "VerifiedCompilation" :| "Trace" : [], [])
      , (Open, "VerifiedCompilation" :| "Certificate" : [], [])
      , (Open, "Utils" :| [], [])
      ]

mkAgdaAstFile :: Int -> UTerm -> Maybe (OptStage, Hints) -> (ModuleName, String)
mkAgdaAstFile n pre mHints =
  ( modName
  , unlines $
      [ "module " <> toIdent modName <> " where"
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
          Just (_, hints) ->
            [ ""
            , "hints : Hints"
            , "hints = " <> renderAgdaUnparse hints
            ]
          Nothing -> []
  )
  where
    modName = astModName n

newtype AgdaVar = AgdaVar String
  deriving (IsString)

qualify :: ModuleName -> AgdaVar -> AgdaVar
qualify modName (AgdaVar x) = AgdaVar (toIdent modName ++ "." ++ x)

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
      ++ map renderImport (astImports ++ proofImports)
      ++ [ ""
         , "trace : Trace (0 ⊢)"
         , "trace ="
         ]
      ++ map ("  " ++) (printTrace traceExpr)
      ++ [ ""
         , "certificate : Certificate trace"
         , "certificate = "
         , renderProof proofExpr
         ]
  where
    astImports :: [Import]
    astImports = map (\n -> (Closed, astModName n, [])) [0 .. length certTrace - 1]

    proofImports :: [Import]
    proofImports = map (\n -> (Closed, proofModName n, [])) [0 .. length certTrace - 2]

    -- Replace hints and ASTs in the trace by agda variables that point to the right definition
    traceExpr :: NonEmptySep (OptStage, AgdaVar) AgdaVar
    traceExpr = go 0 certTrace
      where
        go n (Singleton _) = Singleton (qualify (astModName n) (AgdaVar "ast"))
        go n (Cons _ (stage, _) xs) =
          Cons
            (qualify (astModName n) "ast")
            (stage, qualify (astModName n) "hints")
            (go (n + 1) xs)

    -- Non-empty list of variables that point to the proofs per pass
    proofExpr :: NonEmpty AgdaVar
    proofExpr = go 0 certTrace
      where
        go _ (Singleton _) = AgdaVar "tt" :| []
        go n (Cons _ _ xs) = cons (qualify (proofModName n) (AgdaVar "related")) (go (n + 1) xs)

-- Print the imported proofs as a big product
renderProof :: NonEmpty AgdaVar -> String
renderProof (AgdaVar x :| xs) =
  unlines $
    [("  ( " ++ x)]
      ++ map (\(AgdaVar p) -> "  , " ++ p) xs
      ++ [("  )")]

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
  , proofModNames :: [(ModuleName, String)]
  , agdalib :: (FilePath, String)
  }

{-| For each term in the trace, create module contents using the given
function, which is also passed the index in the trace. -}
traceToFiles
  :: (Int -> UTerm -> Maybe (OptStage, Hints) -> (ModuleName, String))
  -> Trace UTerm
  -> [(ModuleName, String)]
traceToFiles f t = go 0 t
  where
    go n (Singleton x) = [f n x Nothing]
    go n (Cons x (o, h) xs) = f n x (Just (o, h)) : go (n + 1) xs

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
      astModules = traceToFiles mkAgdaAstFile (certTrace cert)
      proofModNames = traceToFiles proofFile (certTrace cert)
      agdalib = mkAgdaLib name
   in AgdaCertificateProject
        { mainModule = (certName cert <> ".agda", mainModule)
        , astModules
        , proofModNames
        , agdalib
        }

writeCertificateProject
  :: CertDir
  -> AgdaCertificateProject
  -> Certifier ()
writeCertificateProject
  certDir
  AgdaCertificateProject
    { mainModule
    , astModules
    , proofModNames
    , agdalib
    } =
    liftIO $ do
      let (mainModulePath, mainModuleContents) = mainModule
          (agdalibPath, agdalibContents) = agdalib
          certName = takeBaseName mainModulePath
      createDirectoryIfMissing True certDir
      createDirectoryIfMissing True (certDir </> "src")

      -- directory per AST in trace
      for_ (astModules ++ proofModNames) $ \(modName, contents) -> do
        createDirectoryIfMissing True (certDir </> "src" </> moduleDir modName)
        writeFile (certDir </> "src" </> toFilePath modName) contents

      writeFile (certDir </> "src" </> mainModulePath) mainModuleContents
      writeFile (certDir </> agdalibPath) agdalibContents
      let readmeTemplate = $(embedStringFile "file-embed/certificate-README.md")
      writeFile (certDir </> "README.md") (replace "{{NAME}}" certName readmeTemplate)
