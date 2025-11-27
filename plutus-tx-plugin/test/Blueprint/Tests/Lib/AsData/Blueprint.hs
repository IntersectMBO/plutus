{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

{-| This module contains data type declarations to use in blueprints **only**

The problem with using the 'AsData' types in blueprints is that such types are opaque and
do not reveal their schema when deriving a 'HasBlueprintSchema' instance for a blueprint.

To work around this problem we generate a separate data type declaration for each 'AsData' type
and use these in blueprints.

Do not use these types in real validators, instead use the 'AsData' declarations. -}
module Blueprint.Tests.Lib.AsData.Blueprint where

import Blueprint.Tests.Lib.AsData.Decls (datum2)
import PlutusTx.Blueprint.Definition (definitionRef)
import PlutusTx.Blueprint.TH (makeHasSchemaInstance)

$(datum2)

$(makeHasSchemaInstance ''Datum2 [('MkDatum2, 0)])
