{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

module Blueprint.Definition.Fixture where

import Prelude

import GHC.Generics (Generic)
import PlutusTx.Blueprint.Definition (AsDefinitionId, GenericUnroll, Unroll, definitionRef)
import PlutusTx.Blueprint.TH (makeIsDataSchemaIndexed)

newtype T1 = MkT1 Integer
  deriving stock (Generic)

deriving anyclass instance (AsDefinitionId T1)
$(makeIsDataSchemaIndexed ''T1 [('MkT1, 0)])
type instance Unroll T1 = GenericUnroll T1

data T2 = MkT2 T1 T1
  deriving stock (Generic)

deriving anyclass instance (AsDefinitionId T2)
$(makeIsDataSchemaIndexed ''T2 [('MkT2, 0)])
type instance Unroll T2 = GenericUnroll T2
