{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

module Blueprint.Definition.Fixture where

import Prelude

import PlutusTx.Blueprint.Definition (AsDefinitionId, definitionRef)
import PlutusTx.Blueprint.TH (makeIsDataSchemaIndexed)

newtype T1 = MkT1 Integer

deriving anyclass instance (AsDefinitionId T1)
$(makeIsDataSchemaIndexed ''T1 [('MkT1, 0)])

data T2 = MkT2 T1 T1

deriving anyclass instance (AsDefinitionId T2)
$(makeIsDataSchemaIndexed ''T2 [('MkT2, 0)])
