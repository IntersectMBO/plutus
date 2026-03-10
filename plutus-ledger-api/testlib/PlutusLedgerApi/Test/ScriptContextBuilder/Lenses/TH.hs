{-# LANGUAGE ImplicitPrelude #-}

module PlutusLedgerApi.Test.ScriptContextBuilder.Lenses.TH
  ( makeLensesWithL
  ) where

import Control.Lens qualified as L
import Language.Haskell.TH (DecsQ, Name)

{-| Uses 'makeLensesWith' to automatically create lens fields, but adds the 'L'
suffix to each lens field name. -}
makeLensesWithL :: Name -> DecsQ
makeLensesWithL = L.makeLensesWith (L.defaultFieldRules L.& L.lensField L..~ L.mappingNamer (\s -> [s ++ "L"]))
