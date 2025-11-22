{-# LANGUAGE TemplateHaskellQuotes #-}

{-| This module contains TH data type declarations from which 'AsData' declarations are derived.

These declarations are used for two purposes:
1. To generate an 'AsData' type declaration to be used in real validators.
2. To generate a regular data type declaration to be used in a blueprint.

Because of the GHC stage restriction, we have to keep these TH declarations in a separate module. -}
module Blueprint.Tests.Lib.AsData.Decls where

import GHC.Generics (Generic)
import Language.Haskell.TH qualified as TH
import PlutusTx.Blueprint.Definition (HasBlueprintDefinition)

datum2 :: TH.DecsQ
datum2 =
  [d|
    data Datum2 = MkDatum2 {datum2integer :: Integer, datum2bool :: Bool}
      deriving stock (Generic)
      deriving anyclass (HasBlueprintDefinition)
    |]
