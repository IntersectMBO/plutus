{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternSynonyms #-}

module PlutusTx.Compiler.Compat where

import GHC.Core.Class qualified as GHC
import GHC.Hs.Expr qualified as GHC
import GHC.Hs.Extension qualified as GHC
import GHC.Types.Id.Info qualified as GHC
import Language.Haskell.Syntax.Binds qualified as GHC
import Language.Haskell.Syntax.Extension qualified as GHC
import Language.Haskell.Syntax.Type qualified as GHC
#if __GLASGOW_HASKELL__ < 910
import GHC.Parser.Annotation qualified as GHC
#endif
#if __GLASGOW_HASKELL__ < 912
import GHC.Data.Bag qualified as GHC
#endif

maybeGetClassOpId :: GHC.IdDetails -> Maybe GHC.Class
#if __GLASGOW_HASKELL__ >= 912
maybeGetClassOpId (GHC.ClassOpId cls _) = Just cls
maybeGetClassOpId _ = Nothing
#else
maybeGetClassOpId (GHC.ClassOpId cls) = Just cls
maybeGetClassOpId _ = Nothing
#endif

hsAppTc :: GHC.LHsExpr GHC.GhcTc -> GHC.LHsExpr GHC.GhcTc -> GHC.HsExpr GHC.GhcTc
#if __GLASGOW_HASKELL__ >= 910
hsAppTc = GHC.HsApp GHC.noExtField
#else
hsAppTc = GHC.HsApp GHC.EpAnnNotUsed
#endif

pattern HsAppType
  :: GHC.XAppTypeE (GHC.GhcPass p)
  -> GHC.LHsExpr (GHC.GhcPass p)
  -> GHC.LHsWcType (GHC.NoGhcTc (GHC.GhcPass p))
  -> GHC.HsExpr (GHC.GhcPass p)
#if __GLASGOW_HASKELL__ >= 910
pattern HsAppType x expr ty <- GHC.HsAppType x expr ty
  where
    HsAppType x expr ty = GHC.HsAppType x expr ty
#else
pattern HsAppType x expr ty <- GHC.HsAppType x expr _ ty
  where
    HsAppType x expr ty = GHC.HsAppType x expr GHC.noHsTok ty
#endif

pattern WrapExpr
  :: GHC.HsExpr GHC.GhcTc -> GHC.XXExprGhcTc
#if __GLASGOW_HASKELL__ >= 912
pattern WrapExpr e <- GHC.WrapExpr _ e
#else
pattern WrapExpr e <- GHC.WrapExpr (GHC.HsWrap _ e)
#endif

pattern HsPar :: GHC.LHsExpr GHC.GhcTc -> GHC.HsExpr GHC.GhcTc
#if __GLASGOW_HASKELL__ >= 912
pattern HsPar e <- GHC.HsPar _ e
#else
pattern HsPar e <- GHC.HsPar _ _ e _
#endif

modifyBinds :: ([GHC.LHsBindLR p p] -> [GHC.LHsBindLR p p]) -> GHC.LHsBinds p -> GHC.LHsBinds p
#if __GLASGOW_HASKELL__ >= 912
modifyBinds = ($)
#else
-- We need this because for some reason `transformBi` does not work on `Bag`,
-- even though `Bag` has a `Data` instance. It it perhaps because the `Data`
-- instance for `Bag` is buggy.
modifyBinds f = GHC.listToBag . f . GHC.bagToList
#endif
