module PlutusTx.Plugin.Deriving.Type.Field
  ( Field (..)
  , make
  , isOptional
  )
where

import GHC.Hs qualified as Ghc
import GHC.Plugins qualified as Ghc
import PlutusTx.Plugin.Deriving.Hs (pattern Loc)
import PlutusTx.Plugin.Deriving.Hsc qualified as Hsc

data Field = Field
  { name :: Ghc.OccName
  , type_ :: Ghc.HsType Ghc.GhcPs
  }

make
  :: Ghc.SrcSpan
  -> Ghc.LHsType Ghc.GhcPs
  -> Ghc.LFieldOcc Ghc.GhcPs
  -> Ghc.Hsc Field
make srcSpan (Loc lHsType) (Loc lFieldOcc) = case lFieldOcc of
  Ghc.FieldOcc _ (Loc (Ghc.Unqual occName)) ->
    pure Field {name = occName, type_ = lHsType}
  Ghc.FieldOcc _ _ ->
    Hsc.throwError srcSpan $ Ghc.text "unsupported RdrName"

isOptional :: Field -> Bool
isOptional field
  | Ghc.HsAppTy _ (Loc hsType) _ <- type_ field
  , Ghc.HsTyVar _ _ (Loc rdrName) <- hsType
  , Ghc.Unqual occName <- rdrName =
      Ghc.occNameString occName == "Maybe"
  | otherwise =
      False
