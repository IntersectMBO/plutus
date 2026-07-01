{-# LANGUAGE CPP #-}

module PlutusTx.Plugin.Deriving.Type.Type
  ( Type (..)
  , make
  , qualifiedName
  )
where

import Control.Monad qualified as Monad
#if __GLASGOW_HASKELL__ >= 910
import qualified PlutusTx.Plugin.Deriving.Hsc as Hsc
#endif
import GHC.Hs qualified as Ghc
import GHC.Plugins qualified as Ghc
import PlutusTx.Plugin.Deriving.Type.Constructor qualified as Constructor

data Type = Type
  { name :: Ghc.IdP Ghc.GhcPs
  , variables :: [Ghc.IdP Ghc.GhcPs]
  , constructors :: [Constructor.Constructor]
  }

make
  :: Ghc.LIdP Ghc.GhcPs
  -> Ghc.LHsQTyVars Ghc.GhcPs
  -> [Ghc.LConDecl Ghc.GhcPs]
  -> Ghc.SrcSpan
  -> Ghc.Hsc Type
make lIdP lHsQTyVars lConDecls srcSpan = do
  lHsTyVarBndrs <- case lHsQTyVars of
    Ghc.HsQTvs _ hsq_explicit -> pure hsq_explicit
  theVariables <- Monad.forM lHsTyVarBndrs $ extractTyVar srcSpan
  theConstructors <- mapM (Constructor.make srcSpan) lConDecls
  pure
    Type
      { name = Ghc.unLoc lIdP
      , variables = theVariables
      , constructors = theConstructors
      }

{-| Extract the variable name from one type-variable binder. The binder layout
changed to @HsTvb@/@HsBndrVar@ in GHC 9.10. -}
extractTyVar
  :: Ghc.SrcSpan
  -> Ghc.LHsTyVarBndr ext Ghc.GhcPs
  -> Ghc.Hsc (Ghc.IdP Ghc.GhcPs)
#if __GLASGOW_HASKELL__ >= 910
extractTyVar srcSpan lHsTyVarBndr = case Ghc.unLoc lHsTyVarBndr of
  Ghc.HsTvb _ _ (Ghc.HsBndrVar _ (Ghc.L _ var)) _ -> pure var
  -- HsBndrWildCard and the XTyVarBndr extension constructor
  _ -> Hsc.throwError srcSpan $ Ghc.text "unknown type variable binder"
#else
extractTyVar _srcSpan lHsTyVarBndr = case Ghc.unLoc lHsTyVarBndr of
  Ghc.UserTyVar _ _ (Ghc.L _ var) -> pure var
  Ghc.KindedTyVar _ _ (Ghc.L _ var) _ -> pure var
#endif

qualifiedName :: Ghc.ModuleName -> Type -> String
qualifiedName moduleName type_ =
  mconcat
    [ Ghc.moduleNameString moduleName
    , "."
    , Ghc.occNameString . Ghc.rdrNameOcc $ name type_
    ]
