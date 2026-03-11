{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

module PlutusTx.Plugin.Unsupported where

import PlutusTx.Compiler.Compat qualified as Compat
import PlutusTx.Compiler.Expr
import PlutusTx.Eq qualified
import PlutusTx.Ord qualified
import PlutusTx.Plugin.Utils qualified

import GHC.Builtin.Names qualified as GHC
import GHC.Core.TyCo.Rep qualified as GHC
import GHC.Hs qualified as GHC
import GHC.Hs.Syn.Type qualified as GHC
import GHC.Iface.Env qualified as GHC
import GHC.Plugins qualified as GHC
import GHC.Tc.Types qualified as GHC
import GHC.Tc.Types.Evidence qualified as GHC
import GHC.Tc.Utils.Env qualified as GHC
import GHC.Tc.Utils.Monad qualified as GHC
import GHC.Unit.Finder qualified as GHC

import Control.Monad.IO.Class
import Data.Foldable
import Data.Generics.Uniplate.Data
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe
import Language.Haskell.TH qualified as TH

type Module = String
type Class = String
type Method = String
type UseThisInstead = Maybe String

data Unsupported
  = BaseMethod Class Method UseThisInstead
  | IO

renderUnsupported :: Unsupported -> String
renderUnsupported = \case
  BaseMethod cls method malt ->
    (cls <> "." <> method)
      <> case malt of Just alt -> ", use " <> alt; Nothing -> ""
  IO -> "IO actions are not supported in Plinth"

isUnsupported :: GHC.HsExpr GHC.GhcTc -> Maybe Unsupported
isUnsupported expr =
  asum
    [ checkUnsupportedMethod expr
    , checkIO ty
    ]
  where
    ty = GHC.hsExprType expr

-- | Check if the type involves IO.
checkIO :: GHC.Type -> Maybe Unsupported
checkIO ty = case GHC.splitTyConApp_maybe ty of
  Just (tc, _) | GHC.getName tc == GHC.ioTyConName -> Just IO
  _ -> do
    (_, _, arg, res) <- GHC.splitFunTy_maybe ty
    asum [checkIO arg, checkIO res]

-- | Check if an expr is a method of an unsupported @base@ class.
checkUnsupportedMethod :: GHC.HsExpr GHC.GhcTc -> Maybe Unsupported
checkUnsupportedMethod = \case
  GHC.HsVar _ (GHC.L _ v)
    | Just cls <- GHC.getName <$> GHC.isClassOpId_maybe v
    , (Just modu, occ) <- splitGhcName cls
    , Just alt <- Map.lookup (modu, occ) unsupportedBaseClasses ->
        Just $ BaseMethod (modu <> "." <> occ) (renderGhcName $ GHC.getName v) alt
    | otherwise -> Nothing
  GHC.XExpr (Compat.WrapExpr e) -> checkUnsupportedMethod e
  _ -> Nothing

renderGhcName :: GHC.Name -> String
renderGhcName = GHC.showSDocUnsafe . GHC.pprName
{-# INLINE renderGhcName #-}

splitGhcName :: GHC.Name -> (Maybe Module, String)
splitGhcName name = (modu, occ)
  where
    modu = fmap (GHC.moduleNameString . GHC.moduleName) (GHC.nameModule_maybe name)
    occ = GHC.occNameString (GHC.nameOccName name)
{-# INLINE splitGhcName #-}

unsupportedBaseClasses :: Map (Module, Class) UseThisInstead
unsupportedBaseClasses =
  Map.fromList
    . mapMaybe
      ( \(name, alt) -> do
          modu <- TH.nameModule name
          pure ((modu, TH.nameBase name), TH.pprint <$> alt)
      )
    $ [ (''Prelude.Eq, Just ''PlutusTx.Eq.Eq)
      , (''Prelude.Ord, Just ''PlutusTx.Ord.Ord)
      ]

unsupportedMarkerModule, unsupportedMarkerName :: String
unsupportedMarkerModule = fromJust $ TH.nameModule 'PlutusTx.Plugin.Utils.unsupported
unsupportedMarkerName = TH.nameBase 'PlutusTx.Plugin.Utils.unsupported

injectUnsupportedMarkers
  :: GHC.TcGblEnv
  -> GHC.TcM GHC.TcGblEnv
injectUnsupportedMarkers env = do
  hscEnv <- GHC.getTopEnv
  findResult <-
    liftIO $
      GHC.findImportedModule
        hscEnv
        (GHC.mkModuleName unsupportedMarkerModule)
        GHC.NoPkgQual
  unsupportedId <- case findResult of
    GHC.Found _ m -> do
      GHC.tcLookupId =<< GHC.lookupOrig m (GHC.mkVarOcc unsupportedMarkerName)
    _ ->
      GHC.pprPanic
        "Plinth Compiler"
        (GHC.text $ "Could not find module " <> unsupportedMarkerModule)
  let binds = GHC.tcg_binds env
      binds' = Compat.modifyBinds (transformBi (wrapUnsupported unsupportedId)) binds
  pure env {GHC.tcg_binds = binds'}

wrapUnsupported :: GHC.Id -> GHC.LHsExpr GHC.GhcTc -> GHC.LHsExpr GHC.GhcTc
wrapUnsupported unsupportedId le@(GHC.L ann e)
  | Just unsupported <- isUnsupported e
  , Just sp <- GHC.srcSpanToRealSrcSpan (GHC.locA ann) =
      let msgTy = GHC.LitTy . GHC.StrTyLit . GHC.mkFastString $ renderUnsupported unsupported
          locTy = GHC.LitTy . GHC.StrTyLit . GHC.mkFastString $ encodeSrcSpan sp
          ty = GHC.hsExprType e
          wrapper =
            GHC.WpTyApp ty
              `GHC.WpCompose` GHC.WpTyApp locTy
              `GHC.WpCompose` GHC.WpTyApp msgTy
          wrapped = GHC.mkHsWrap wrapper (GHC.HsVar GHC.noExtField (GHC.noLocA unsupportedId))
       in GHC.noLocA $ Compat.hsAppTc (GHC.noLocA wrapped) le
  | otherwise = le
