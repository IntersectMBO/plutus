{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module PlutusIR.Test
    ( module PlutusIR.Test
    , initialSrcSpan
    , topSrcSpan
    , rethrow
    , PLC.prettyPlcClassicSimple
    ) where

import PlutusPrelude
import Test.Tasty.Extras

import Control.Exception
import Control.Lens hiding (op, transform)
import Control.Monad.Except
import Control.Monad.Morph (hoist)
import Control.Monad.Reader as Reader

import PlutusCore.Annotation qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Core qualified as PLC
import PlutusCore.DeBruijn qualified as PLC
import PlutusCore.Default qualified as PLC
import PlutusCore.Error (ParserErrorBundle)
import PlutusCore.Error qualified as PLC
import PlutusCore.Pretty
import PlutusCore.Pretty qualified as PLC
import PlutusCore.Quote (runQuoteT)
import PlutusCore.Test hiding (ppCatch)
import PlutusCore.TypeCheck qualified as PLC
import PlutusIR as PIR
import PlutusIR.Analysis.Builtins
import PlutusIR.Compiler as PIR
import PlutusIR.Parser (Parser, pTerm, parse)
import PlutusIR.Transform.RewriteRules
import PlutusIR.TypeCheck
import System.FilePath (joinPath, splitExtension, (</>))

import Data.Hashable
import Data.Text qualified as T
import Data.Text.IO qualified as T

import Prettyprinter
import Prettyprinter.Render.Text

instance
  ( PLC.GEq uni
  , PLC.Typecheckable uni fun
  , PLC.CaseBuiltin uni
  , PLC.PrettyUni uni
  , Pretty fun
  , Pretty a
  , Typeable a
  , Ord a
  , PLC.AnnInline a
  , Default (PLC.CostingPart uni fun)
  , Default (BuiltinsInfo uni fun)
  , Default (RewriteRules uni fun)
  ) =>
  ToTPlc (PIR.Program PIR.TyName PIR.Name uni fun a) uni fun
  where
  toTPlc = asIfThrown . fmap void . compileWithOpts id

instance
  ( PLC.GEq uni
  , uni `PLC.Everywhere` Eq
  , PLC.Typecheckable uni fun
  , PLC.CaseBuiltin uni
  , PLC.PrettyUni uni
  , Pretty fun
  , Hashable fun
  , Pretty a
  , Typeable a
  , Ord a
  , PLC.AnnInline a
  , Default (PLC.CostingPart uni fun)
  , Default (BuiltinsInfo uni fun)
  , Default (RewriteRules uni fun)
  ) =>
  ToUPlc (PIR.Program PIR.TyName PIR.Name uni fun a) uni fun
  where
  toUPlc = toTPlc >=> toUPlc

instance PLC.AnnInline PLC.SrcSpan where
  annAlwaysInline = PLC.SrcSpan mempty 0 0 0 0
  annSafeToInline = PLC.SrcSpan mempty 0 0 0 0
  annMayInline = PLC.SrcSpan mempty 0 0 0 0

instance PLC.AnnInline PLC.SrcSpans where
  annAlwaysInline = mempty
  annSafeToInline = mempty
  annMayInline = mempty

pTermAsProg :: Parser (PIR.Program PIR.TyName PIR.Name PLC.DefaultUni PLC.DefaultFun PLC.SrcSpan)
pTermAsProg = fmap (PIR.Program mempty PLC.latestVersion) pTerm

{- | Adapt an computation that keeps its errors in an 'Except' into one that looks as if
it caught them in 'IO'.
-}
asIfThrown ::
  (Exception e) =>
  Except e a ->
  ExceptT SomeException IO a
asIfThrown = withExceptT SomeException . hoist (pure . runIdentity)

compileWithOpts ::
  ( PLC.GEq uni
  , PLC.Typecheckable uni fun
  , PLC.CaseBuiltin uni
  , Ord a
  , PLC.AnnInline a
  , PLC.PrettyUni uni
  , PLC.Pretty fun
  , PLC.Pretty a
  , Default (BuiltinsInfo uni fun)
  , Default (PLC.CostingPart uni fun)
  , Default (RewriteRules uni fun)
  ) =>
  (CompilationCtx uni fun a -> CompilationCtx uni fun a) ->
  PIR.Program PIR.TyName PIR.Name uni fun a ->
  Except
    (PIR.Error uni fun (PIR.Provenance a))
    (PLC.Program PIR.TyName PIR.Name uni fun (PIR.Provenance a))
compileWithOpts optsMod pir = do
  tcConfig <- modifyError PIR.PLCTypeError $ PLC.getDefTypeCheckConfig noProvenance
  let pirCtx = optsMod (toDefaultCompilationCtx tcConfig)
  flip runReaderT pirCtx $ runQuoteT $ do
    compiled <- compileProgram pir
    -- PLC errors are parameterized over PLC.Terms, whereas PIR errors over PIR.Terms
    -- and as such, these prism errors cannot be unified.
    -- We instead run the ExceptT, collect any PLC error and explicitly lift into a PIR
    -- error by wrapping with PIR._PLCError
    _plcConcrete <- modifyError (PLCError . PLC.TypeErrorE) $ PLC.inferTypeOfProgram tcConfig compiled
    pure compiled

withGoldenFileM :: String -> (T.Text -> IO T.Text) -> TestNested
withGoldenFileM name op = do
  dir <- currentDir
  let testFile = dir </> name
      goldenFile = dir </> base ++ ".golden" ++ ext
  embed $ goldenVsTextM name goldenFile (op =<< T.readFile testFile)
  where
    currentDir = joinPath <$> ask
    (base, ext) = splitExtension name

-- TODO: deduplicate with the Plutus Core one
ppCatch :: (a -> Doc ann) -> ExceptT SomeException IO a -> IO T.Text
ppCatch toDoc value = render . either (pretty . show) toDoc <$> runExceptT value

goldenPir :: (PrettyPlc b) => (a -> b) -> Parser a -> String -> TestNested
goldenPir op = goldenPirM (return . op)

goldenPirUnique :: (Pretty b) => (a -> b) -> Parser a -> String -> TestNested
goldenPirUnique op = goldenPirMUnique (return . op)

goldenPirDoc :: (a -> Doc ann) -> Parser a -> String -> TestNested
goldenPirDoc op = goldenPirDocM (return . op)

goldenPirMUnique :: forall a b. (Pretty b) => (a -> IO b) -> Parser a -> String -> TestNested
goldenPirMUnique op parser name = withGoldenFileM name parseOrError
  where
    parseOrError :: T.Text -> IO T.Text
    parseOrError =
      let parseTxt :: T.Text -> Either ParserErrorBundle a
          parseTxt txt = runQuoteT $ parse parser name txt
       in either (return . display) (fmap display . op) . parseTxt

goldenPirM :: forall a b. (PrettyPlc b) => (a -> IO b) -> Parser a -> String -> TestNested
goldenPirM op parser name = withGoldenFileM name parseOrError
  where
    parseOrError :: T.Text -> IO T.Text
    parseOrError =
      let parseTxt :: T.Text -> Either ParserErrorBundle a
          parseTxt txt = runQuoteT $ parse parser name txt
       in either (pure . display) ((render . prettyPlcReadableSimple <$>) . op) . parseTxt

goldenPirDocM :: forall a ann. (a -> IO (Doc ann)) -> Parser a -> String -> TestNested
goldenPirDocM op parser name = withGoldenFileM name parseOrError
  where
    parseOrError :: T.Text -> IO T.Text
    parseOrError =
      let parseTxt :: T.Text -> Either ParserErrorBundle a
          parseTxt txt = runQuoteT $ parse parser name txt
       in either (return . display) (fmap (renderStrict . layoutPretty defaultLayoutOptions) . op)
            . parseTxt

goldenPlcFromPir ::
  (ToTPlc a PLC.DefaultUni PLC.DefaultFun) =>
  Parser a ->
  String ->
  TestNested
goldenPlcFromPir = goldenPirM $ \ast -> ppCatch prettyPlcReadableSimple $ do
  p <- toTPlc ast
  withExceptT @_ @PLC.FreeVariableError toException $ traverseOf PLC.progTerm PLC.deBruijnTerm p

goldenPlcFromPirScott ::
  (Ord a, Typeable a, Pretty a, PLC.AnnInline a
  , prog ~ PIR.Program PIR.TyName PIR.Name PLC.DefaultUni PLC.DefaultFun a) =>
  Parser prog ->
  String ->
  TestNested
goldenPlcFromPirScott = goldenPirM $ \ast -> ppCatch prettyPlcReadableSimple $ do
  p <-
    asIfThrown
      . fmap void
      . compileWithOpts (set (PIR.ccOpts . PIR.coDatatypes . PIR.dcoStyle) ScottEncoding)
      $ ast
  withExceptT @_ @PLC.FreeVariableError toException $ traverseOf PLC.progTerm PLC.deBruijnTerm p

goldenNamedUPlcFromPir ::
  (ToUPlc a PLC.DefaultUni PLC.DefaultFun) =>
  Parser a ->
  String ->
  TestNested
goldenNamedUPlcFromPir = goldenPirM $ ppCatch prettyPlcReadableSimple . toUPlc

goldenEvalPir ::
  (ToUPlc a PLC.DefaultUni PLC.DefaultFun) =>
  Parser a ->
  String ->
  TestNested
goldenEvalPir = goldenPirM (\ast -> ppCatch prettyPlcReadableSimple $ runUPlc [ast])

goldenTypeFromPir ::
  forall a.
  (Pretty a, Typeable a) =>
  a ->
  Parser (Term PIR.TyName PIR.Name PLC.DefaultUni PLC.DefaultFun a) ->
  String ->
  TestNested
goldenTypeFromPir x =
  goldenPirM $ \ast -> ppCatch prettyPlcReadable $
    withExceptT (toException :: PIR.Error PLC.DefaultUni PLC.DefaultFun a -> SomeException) $
      runQuoteT $ do
        tcConfig <- modifyError (PLCError . PLC.TypeErrorE) $ getDefTypeCheckConfig x
        inferType tcConfig ast
