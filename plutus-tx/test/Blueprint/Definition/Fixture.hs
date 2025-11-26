{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Blueprint.Definition.Fixture where

import Prelude

import GHC.Generics (Generic)
import PlutusTx.Blueprint.Definition (HasBlueprintDefinition, definitionRef)
import PlutusTx.Blueprint.TH (makeIsDataSchemaIndexed)

newtype T1 = MkT1 Integer

deriving stock instance Generic T1
deriving anyclass instance HasBlueprintDefinition T1
$(makeIsDataSchemaIndexed ''T1 [('MkT1, 0)])

data T2 = MkT2 T1 T1

deriving stock instance Generic T2
deriving anyclass instance HasBlueprintDefinition T2
$(makeIsDataSchemaIndexed ''T2 [('MkT2, 0)])
