module PlutusTx.Plugin.Deriving.Type.Constructor
  ( Constructor (..)
  , make
  )
where

import Data.List qualified as List
import Data.Traversable (for)
import GHC.Hs qualified as Ghc
import GHC.Plugins qualified as Ghc
import PlutusTx.Plugin.Deriving.Hs (pattern Loc)
import PlutusTx.Plugin.Deriving.Hsc qualified as Hsc
import PlutusTx.Plugin.Deriving.Type.Field qualified as Field

data Constructor = Constructor
  { name :: Ghc.IdP Ghc.GhcPs
  , fields :: [Field.Field]
  }

make :: Ghc.SrcSpan -> Ghc.LConDecl Ghc.GhcPs -> Ghc.Hsc Constructor
make srcSpan (Loc lConDecl) = do
  (lIdP, hsConDeclDetails) <- case lConDecl of
    Ghc.ConDeclH98 _ (Loc idP) _ _ _ y _ -> pure (idP, y)
    _ -> Hsc.throwError srcSpan $ Ghc.text "unsupported LConDecl"
  theFields <- case hsConDeclDetails of
    Ghc.RecCon (Loc lConDeclFields) ->
      concat
        <$> for lConDeclFields \(Loc (Ghc.ConDeclField _ lFieldOccs lHsType _)) ->
          for lFieldOccs (Field.make srcSpan lHsType)
    Ghc.PrefixCon _ scaledTypes ->
      pure $
        List.zipWith
          ( \i (Ghc.HsScaled _ (Loc hsType)) ->
              Field.Field
                { Field.name = Ghc.mkVarOcc ("_field" <> show (i :: Int))
                , Field.type_ = hsType
                }
          )
          [0 ..]
          scaledTypes
    _ -> Hsc.throwError srcSpan $ Ghc.text "unsupported HsConDeclDetails"
  pure Constructor {name = lIdP, fields = theFields}
