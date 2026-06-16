{-# LANGUAGE CPP #-}

module PlutusTx.Plugin.Deriving.Type.Type
  ( Type (..)
  , make
  , qualifiedName
  )
where

import Control.Monad qualified as Monad
import Data.Traversable (for)
#if __GLASGOW_HASKELL__ >= 910
import qualified PlutusTx.Plugin.Deriving.Hsc as Hsc
#endif
import GHC.Hs qualified as Ghc
import GHC.Plugins qualified as Ghc
import PlutusTx.Plugin.Deriving.Hs (pattern Loc)
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
make (Loc lIdP) (Ghc.HsQTvs _ lHsTyVarBndrs) lConDecls srcSpan = do
  theVariables <- for lHsTyVarBndrs $ extractTyVar srcSpan
  theConstructors <- for lConDecls $ Constructor.make srcSpan
  pure
    Type
      { name = lIdP
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
  Ghc.HsTvb _ _ (Ghc.HsBndrVar _ (Loc var)) _ -> pure var
  -- HsBndrWildCard and the XTyVarBndr extension constructor
  _ -> Hsc.throwError srcSpan $ Ghc.text "unknown type variable binder"
#else
extractTyVar _srcSpan lHsTyVarBndr = case Ghc.unLoc lHsTyVarBndr of
  Ghc.UserTyVar   _ _ (Loc var)   -> pure var
  Ghc.KindedTyVar _ _ (Loc var) _ -> pure var
#endif

qualifiedName :: Ghc.ModuleName -> Type -> String
qualifiedName moduleName type_ =
  mconcat
    [ Ghc.moduleNameString moduleName
    , "."
    , Ghc.occNameString . Ghc.rdrNameOcc $ name type_
    ]
