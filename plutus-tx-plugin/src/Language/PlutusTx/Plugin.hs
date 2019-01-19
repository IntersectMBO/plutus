{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE ViewPatterns               #-}
{-# OPTIONS_GHC -Wno-unused-foralls #-}
module Language.PlutusTx.Plugin (
    CompiledCode,
    getSerializedPlc,
    getSerializedPir,
    getPlc,
    getPir,
    plugin,
    plc) where

import           Language.PlutusTx.Compiler.Builtins
import           Language.PlutusTx.Compiler.Error
import           Language.PlutusTx.Compiler.Expr
import           Language.PlutusTx.Compiler.Types
import           Language.PlutusTx.Compiler.Utils
import qualified Language.PlutusTx.Lift.Class           as Lift
import           Language.PlutusTx.PIRTypes
import           Language.PlutusTx.PLCTypes
import           Language.PlutusTx.Utils

import qualified GhcPlugins                             as GHC
import qualified Panic                                  as GHC

import qualified Language.PlutusCore                    as PLC
import qualified Language.PlutusCore.Constant           as PLC
import qualified Language.PlutusCore.Constant.Dynamic   as PLC
import           Language.PlutusCore.Quote

import qualified Language.PlutusIR                      as PIR
import qualified Language.PlutusIR.Compiler             as PIR
import qualified Language.PlutusIR.Compiler.Definitions as PIR
import qualified Language.PlutusIR.Optimizer.DeadCode   as PIR

import           Language.Haskell.TH.Syntax             as TH

import           Codec.Serialise                        (DeserialiseFailure, deserialiseOrFail, serialise)
import           Control.Exception
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Reader

import qualified Data.ByteString                        as BS
import qualified Data.ByteString.Lazy                   as BSL
import qualified Data.ByteString.Unsafe                 as BSUnsafe
import qualified Data.Map                               as Map
import qualified Data.Text.Prettyprint.Doc              as PP

import           GHC.TypeLits
import           System.IO.Unsafe                       (unsafePerformIO)

-- | A compiled Plutus Tx program. The type parameter inicates
-- the type of the Haskell expression that was compiled, and
-- hence the type of the compiled code.
data CompiledCode a = CompiledCode {
    serializedPlc   :: BS.ByteString
    , serializedPir :: BS.ByteString
    }

-- Note that we do *not* have a TypeablePlc instance, since we don't know what the type is. We could in principle store it after the plugin
-- typechecks the code, but we don't currently.
instance Lift.Lift (CompiledCode a) where
    lift (getPlc -> (PLC.Program () _ body)) = PIR.embedIntoIR <$> PLC.rename body

getSerializedPlc :: CompiledCode a -> BSL.ByteString
getSerializedPlc = BSL.fromStrict . serializedPlc

getSerializedPir :: CompiledCode a -> BSL.ByteString
getSerializedPir = BSL.fromStrict . serializedPir

{- Note [Deserializing the AST]
The types suggest that we can fail to deserialize the AST that we embedded in the program.
However, we just did it ourselves, so this should be impossible, and we signal this with an
exception.
-}
newtype ImpossibleDeserialisationFailure = ImpossibleDeserialisationFailure DeserialiseFailure
instance Show ImpossibleDeserialisationFailure where
    show (ImpossibleDeserialisationFailure e) = "Failed to deserialise our own program! This is a bug, please report it. Caused by: " ++ show e
instance Exception ImpossibleDeserialisationFailure

getPlc :: CompiledCode a -> PLC.Program PLC.TyName PLC.Name ()
getPlc wrapper = case deserialiseOrFail $ getSerializedPlc wrapper of
    Left e  -> throw $ ImpossibleDeserialisationFailure e
    Right p -> p

getPir :: CompiledCode a -> PIR.Program PIR.TyName PIR.Name ()
getPir wrapper = case deserialiseOrFail $ getSerializedPir wrapper of
    Left e  -> throw $ ImpossibleDeserialisationFailure e
    Right p -> p

-- | Marks the given expression for conversion to PLC.
plc :: forall (loc::Symbol) a . a -> CompiledCode a
-- this constructor is only really there to get rid of the unused warning
plc _ = CompiledCode mustBeReplaced mustBeReplaced

data PluginOptions = PluginOptions {
    poDoTypecheck    :: Bool
    , poDeferErrors  :: Bool
    , poStripContext :: Bool
    }

plugin :: GHC.Plugin
plugin = GHC.defaultPlugin { GHC.installCoreToDos = install }

install :: [GHC.CommandLineOption] -> [GHC.CoreToDo] -> GHC.CoreM [GHC.CoreToDo]
install args todo =
    let
        opts = PluginOptions {
            poDoTypecheck = notElem "dont-typecheck" args
            , poDeferErrors = elem "defer-errors" args
            , poStripContext = elem "strip-context" args
            }
    in
        pure (GHC.CoreDoPluginPass "Core to PLC" (pluginPass opts) : todo)

pluginPass :: PluginOptions -> GHC.ModGuts -> GHC.CoreM GHC.ModGuts
pluginPass opts guts = getMarkerName >>= \case
    -- nothing to do
    Nothing -> pure guts
    Just name -> GHC.bindsOnlyPass (mapM $ convertMarkedExprsBind opts name) guts

{- Note [Hooking in the plugin]
Working out what to process and where to put it is tricky. We are going to turn the result in
to a 'CompiledCode', not the Haskell expression we started with!

Currently we look for calls to the 'plc :: a -> CompiledCode' function, and we replace the whole application with the
generated code object, which will still be well-typed.

However, if we do this with a polymorphic expression as the argument to 'plc', we have problems
where GHC gives unconstrained type variables the type `Any` rather than leaving them abstracted as we require (see
note [System FC and system FW]). I don't currently know how to resolve this.
-}

getMarkerName :: GHC.CoreM (Maybe GHC.Name)
getMarkerName = GHC.thNameToGhcName 'plc

messagePrefix :: String
messagePrefix = "GHC Core to PLC plugin"

failCompilation :: String -> GHC.CoreM a
failCompilation message = liftIO $ GHC.throwGhcExceptionIO $ GHC.ProgramError $ messagePrefix ++ ": " ++ message

failCompilationSDoc :: String -> GHC.SDoc -> GHC.CoreM a
failCompilationSDoc message sdoc = liftIO $ GHC.throwGhcExceptionIO $ GHC.PprProgramError (messagePrefix ++ ":" ++ message) sdoc

-- | Get the 'GHC.Name' corresponding to the given 'TH.Name', or throw a GHC exception if
-- we can't get it.
thNameToGhcNameOrFail :: TH.Name -> GHC.CoreM GHC.Name
thNameToGhcNameOrFail name = do
    maybeName <- GHC.thNameToGhcName name
    case maybeName of
        Just n  -> pure n
        Nothing -> failCompilation $ "Unable to get Core name needed for the plugin to function: " ++ show name

-- | Create a GHC Core expression that will evaluate to the given ByteString at runtime.
makeByteStringLiteral :: BS.ByteString -> GHC.CoreM GHC.CoreExpr
makeByteStringLiteral bs = do
    flags <- GHC.getDynFlags

    {-
    This entire section will crash horribly in a number of circumstances. Such is life.
    - If any of the names we need can't be found as GHC Names
    - If we then can't look up those GHC Names to get their IDs/types
    - If we make any mistakes creating the Core expression
    -}

    -- Get the names of functions/types that we need for our expression
    upio <- GHC.lookupId =<< thNameToGhcNameOrFail 'unsafePerformIO
    bsTc <- GHC.lookupTyCon =<< thNameToGhcNameOrFail ''BS.ByteString
    upal <- GHC.lookupId =<< thNameToGhcNameOrFail 'BSUnsafe.unsafePackAddressLen

    -- We construct the following expression:
    -- unsafePerformIO $ unsafePackAddressLen <length as int literal> <data as string literal address>
    -- This technique gratefully borrowed from the file-embed package

    -- The flags here are so GHC can check whether the int is in range for the current platform.
    let lenLit = GHC.mkIntExpr flags $ fromIntegral $ BS.length bs
    -- This will have type Addr#, which is right for unsafePackAddressLen
    let bsLit = GHC.Lit (GHC.MachStr bs)
    let upaled = GHC.mkCoreApps (GHC.Var upal) [lenLit, bsLit]
    let upioed = GHC.mkCoreApps (GHC.Var upio) [GHC.Type (GHC.mkTyConTy bsTc), upaled]

    pure upioed

-- | Make a 'BuiltinNameInfo' mapping the given set of TH names to their
-- 'GHC.TyThing's for later reference.
makePrimitiveNameInfo :: [TH.Name] -> GHC.CoreM BuiltinNameInfo
makePrimitiveNameInfo names = do
    mapped <- forM names $ \name -> do
        ghcName <- thNameToGhcNameOrFail name
        thing <- GHC.lookupThing ghcName
        pure (name, thing)
    pure $ Map.fromList mapped

-- | Converts all the marked expressions in the given binder into PLC literals.
convertMarkedExprsBind :: PluginOptions -> GHC.Name -> GHC.CoreBind -> GHC.CoreM GHC.CoreBind
convertMarkedExprsBind opts markerName = \case
    GHC.NonRec b e -> GHC.NonRec b <$> convertMarkedExprs opts markerName e
    GHC.Rec bs -> GHC.Rec <$> mapM (\(b, e) -> (,) b <$> convertMarkedExprs opts markerName e) bs

-- | Converts all the marked expressions in the given expression into PLC literals.
convertMarkedExprs :: PluginOptions -> GHC.Name -> GHC.CoreExpr -> GHC.CoreM GHC.CoreExpr
convertMarkedExprs opts markerName =
    let
        conv = convertMarkedExprs opts markerName
        convB = convertMarkedExprsBind opts markerName
    in \case
      GHC.App (GHC.App (GHC.App
                          -- function id
                          (GHC.Var fid)
                          -- first type argument, must be a string literal type
                          (GHC.Type (GHC.isStrLitTy -> Just fs_locStr)))
                     -- second type argument
                     (GHC.Type codeTy))
            -- value argument
            inner
          | markerName == GHC.idName fid -> convertExpr opts (show fs_locStr) codeTy inner
      e@(GHC.Var fid) | markerName == GHC.idName fid -> failCompilationSDoc "Found invalid marker, not applied correctly" (GHC.ppr e)
      GHC.App e a -> GHC.App <$> conv e <*> conv a
      GHC.Lam b e -> GHC.Lam b <$> conv e
      GHC.Let bnd e -> GHC.Let <$> convB bnd <*> conv e
      GHC.Case e b t alts -> do
            e' <- conv e
            let expAlt (a, bs, rhs) = (,,) a bs <$> conv rhs
            alts' <- mapM expAlt alts
            pure $ GHC.Case e' b t alts'
      GHC.Cast e c -> flip GHC.Cast c <$> conv e
      GHC.Tick t e -> GHC.Tick t <$> conv e
      e@(GHC.Coercion _) -> pure e
      e@(GHC.Lit _) -> pure e
      e@(GHC.Var _) -> pure e
      e@(GHC.Type _) -> pure e

-- TODO: move this somewhere common
stringBuiltinTypes :: PLC.DynamicBuiltinNameTypes
stringBuiltinTypes =
    -- In order to define @trace@ we have to provide a function that actually performs tracing,
    -- but this can't be done once and for all, because we do tracing via 'unsafePerformIO' and 'IORef'
    -- and thus need to either be in the 'IO' monad to create an 'IORef' or create a global 'IORef' via
    -- another 'unsafePerformIO' (perhaps we should do the latter).
    -- Anyway, here we only care about types, so we provide a fake definition of @trace@ that does
    -- nothing just to be able to extract types in a convenient way.
    let fakeTraceDefinition = PLC.dynamicCallAssign (PLC.TypedBuiltinDyn @String) PLC.dynamicTraceName mempty
    in PLC.dynamicBuiltinNameMeaningsToTypes $
       PLC.insertDynamicBuiltinNameDefinition fakeTraceDefinition $
       PLC.insertDynamicBuiltinNameDefinition PLC.dynamicCharToStringDefinition $
       PLC.insertDynamicBuiltinNameDefinition PLC.dynamicAppendDefinition mempty

-- | Actually invokes the Core to PLC compiler to convert an expression into a PLC literal.
convertExpr :: PluginOptions -> String -> GHC.Type -> GHC.CoreExpr -> GHC.CoreM GHC.CoreExpr
convertExpr opts locStr codeTy origE = do
    flags <- GHC.getDynFlags
    -- We need to do this out here, since it has to run in CoreM
    nameInfo <- makePrimitiveNameInfo builtinNames
    let result = withContextM (sdToTxt $ "Converting expr at" GHC.<+> GHC.text locStr) $ do
              (pirP::PIRProgram) <- PIR.Program () . PIR.removeDeadBindings <$> (PIR.runDefT () $ convExprWithDefs origE)
              (plcP::PLCProgram) <- void <$> (flip runReaderT PIR.NoProvenance $ PIR.compileProgram pirP)
              when (poDoTypecheck opts) $ void $
                  PLC.typecheckProgram (PLC.TypeConfig True stringBuiltinTypes mempty mempty Nothing) plcP
              pure (pirP, plcP)
        context = ConvertingContext {
            ccOpts=ConversionOptions { coCheckValueRestriction=poDoTypecheck opts },
            ccFlags=flags,
            ccBuiltinNameInfo=nameInfo,
            ccScopes=initialScopeStack
            }
    case runExcept . runQuoteT . flip runReaderT context $ result of
        Left s ->
            let shown = show $ if poStripContext opts then PP.pretty (stripContext s) else PP.pretty s in
            -- TODO: is this the right way to do either of these things?
            if poDeferErrors opts
            -- this will blow up at runtime
            then do
                tcName <- thNameToGhcNameOrFail ''CompiledCode
                tc <- GHC.lookupTyCon tcName
                pure $ GHC.mkRuntimeErrorApp GHC.rUNTIME_ERROR_ID (GHC.mkTyConApp tc [codeTy]) shown
            -- this will actually terminate compilation
            else failCompilation shown
        Right (pirP, plcP) -> do
            bsLitPir <- makeByteStringLiteral $ BSL.toStrict $ serialise pirP
            bsLitPlc <- makeByteStringLiteral $ BSL.toStrict $ serialise plcP

            dcName <- thNameToGhcNameOrFail 'CompiledCode
            dc <- GHC.lookupDataCon dcName

            pure $
                GHC.Var (GHC.dataConWrapId dc)
                `GHC.App` GHC.Type codeTy
                `GHC.App` bsLitPlc
                `GHC.App` bsLitPir
