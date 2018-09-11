{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TemplateHaskell            #-}

-- See Note [Deserializing the AST]
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Language.Plutus.CoreToPLC.Plugin (PlcCode, getSerializedCode, getAst, plugin, plc) where

import           Language.Plutus.CoreToPLC
import           Language.Plutus.CoreToPLC.Error
import           Language.Plutus.CoreToPLC.Primitives (makePrimitivesMap)

import qualified GhcPlugins                      as GHC

import qualified Language.PlutusCore             as PC
import           Language.PlutusCore.Quote

import           Control.Monad.Except
import           Control.Monad.Reader
import qualified Data.ByteString.Lazy            as BSL
import           Data.Text                       as T

-- Note: we construct this by coercing, so this *must* remain representationally equivalent to '[Word]'
-- unless we change how conversion works, and *must* be abstract.
-- | A PLC program.
newtype PlcCode = PlcCode { unPlc :: [Word] }

getSerializedCode :: PlcCode -> BSL.ByteString
getSerializedCode = BSL.pack . fmap fromIntegral . unPlc

{- Note [Deserializing the AST]
The types suggest that we can fail to deserialize the AST that we embedded in the program.
However, we just did it ourselves, so this should be impossible. Possibly we should surface
the error somehow, but passing it on to the user seems like quite an annoying UI.
-}
getAst :: PlcCode -> PC.Program PC.TyName PC.Name ()
getAst wrapper = let Right p = PC.readProgram $ getSerializedCode wrapper in p

-- | Marks the given expression for conversion to PLC.
plc :: a -> PlcCode
-- this constructor is only really there to get rid of the unused warning
plc _ = PlcCode mustBeReplaced

plugin :: GHC.Plugin
plugin = GHC.defaultPlugin { GHC.installCoreToDos = install }

install :: [GHC.CommandLineOption] -> [GHC.CoreToDo] -> GHC.CoreM [GHC.CoreToDo]
install _ todo = pure (GHC.CoreDoPluginPass "C2C" pluginPass : todo)

pluginPass :: GHC.ModGuts -> GHC.CoreM GHC.ModGuts
pluginPass guts = qqMarkerName >>= \case
    -- nothing to do
    Nothing -> pure guts
    Just name -> GHC.bindsOnlyPass (mapM $ convertMarkedExprsBind name) guts

{- Note [Hooking in the plugin]
Working out what to process and where to put it is tricky. We are going to turn the result in
to a String, or maybe a Bytestring or an AST, either way, not the Haskell expression we started with!

Currently we look for calls to the 'plc :: a -> PLC' function, and we replace the whole application with the
string, which will still be well-typed.

However, if we do this within a single expression, we have problems where GHC gives unconstrained
type variables the type `Any` rather than leaving them abstracted as we require (see
note [System FC and system FW]). I think we can do better but I need to figure out how to actually
look up a name.
-}

qqMarkerName :: GHC.CoreM (Maybe GHC.Name)
qqMarkerName = GHC.thNameToGhcName 'plc

qqMarkerType :: GHC.Type -> Maybe GHC.Type
qqMarkerType vtype = do
    (_, ty) <- GHC.splitForAllTy_maybe vtype
    (_, o) <- GHC.splitFunTy_maybe ty
    pure o

-- | Converts all the marked expressions in the given binder into PLC literals.
convertMarkedExprsBind :: GHC.Name -> GHC.CoreBind -> GHC.CoreM GHC.CoreBind
convertMarkedExprsBind markerName = \case
    GHC.NonRec b e -> GHC.NonRec b <$> convertMarkedExprs markerName e
    GHC.Rec bs -> GHC.Rec <$> mapM (\(b, e) -> (,) b <$> convertMarkedExprs markerName e) bs

-- | Converts all the marked expressions in the given expression into PLC literals.
convertMarkedExprs :: GHC.Name -> GHC.CoreExpr -> GHC.CoreM GHC.CoreExpr
convertMarkedExprs markerName = let
        conv = convertMarkedExprs markerName
        convB = convertMarkedExprsBind markerName
    in \case
      -- the ignored argument is the type for the polymorphic 'plc'
      e@(GHC.App(GHC.App (GHC.Var fid) _) inner) | markerName == GHC.idName fid -> let vtype = GHC.varType fid in
          case qqMarkerType vtype of
              Just t -> convertExpr inner t
              Nothing -> do
                  GHC.errorMsg $ "plc Plugin: found invalid marker, could not decode type:" GHC.$+$ GHC.ppr vtype
                  pure e
      e@(GHC.Var fid) | markerName == GHC.idName fid -> do
            GHC.errorMsg "plc Plugin: found invalid marker, not applied correctly"
            pure e
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
      e@(GHC.Coercion _) -> return e
      e@(GHC.Lit _) -> return e
      e@(GHC.Var _) -> return e
      e@(GHC.Type _) -> return e

-- | Actually invokes the Core to PLC compiler to convert an expression into a PLC literal.
convertExpr :: GHC.CoreExpr -> GHC.Type -> GHC.CoreM GHC.CoreExpr
convertExpr origE tpe = do
    -- Note: tests run with --verbose, so these will appear
    GHC.debugTraceMsg $ "Converting GHC Core expression:" GHC.$+$ GHC.ppr origE
    flags <- GHC.getDynFlags
    prims <- makePrimitivesMap
    let result =
          do
              converted <- convExpr origE
              -- temporarily don't do typechecking due to lack of support for redexes
              --annotated <- convertErrors PCError $ PC.annotateTermQ converted
              --inferredType <- convertErrors PCError $ PC.typecheckTermQ 1000 annotated
              pure (converted, undefined)
    case runExcept $ runReaderT (runQuoteT result) (flags, prims, initialScopeStack) of
        Left s -> do
            GHC.fatalErrorMsg $ "Failed to convert expression:" GHC.$+$ (GHC.text $ T.unpack $ errorText s)
            pure origE
        Right (term, _) -> do
            let termRep = T.unpack $ PC.debugText term
            --let typeRep = T.unpack $ PC.debugText inferredType
            GHC.debugTraceMsg $ "Successfully produced PLC expression:" GHC.$+$ GHC.text termRep --GHC.$+$ "With type:" GHC.$+$ GHC.text typeRep
            let program = PC.Program () (PC.defaultVersion ()) term
            let serialized = PC.writeProgram program
            -- The GHC api only exposes a way to make literals for Words, not Word8s, so we need to convert them
            let (word8s :: [Word]) = fromIntegral <$> BSL.unpack serialized
            -- The flags here are so GHC can check whether the word is in range for the current platform.
            -- This will never actually be a problem for us, since they're really Word8s, but GHC
            -- doesn't know that.
            let (wordExprs :: [GHC.CoreExpr]) = fmap (GHC.mkWordExprWord flags) word8s
            let listExpr = GHC.mkListExpr GHC.wordTy wordExprs
            -- Our result type is representationally equivalent to [Word],
            -- so we can insert a simple coercion here
            pure $ GHC.Cast listExpr $ GHC.mkRepReflCo tpe
