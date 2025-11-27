{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module PlutusTx.IsData.Instances where

import PlutusTx.Blueprint.Definition (definitionRef)
import PlutusTx.Blueprint.TH (makeIsDataSchemaIndexed, unstableMakeIsDataSchema)
import PlutusTx.Bool (Bool (..))
import PlutusTx.Either (Either (..))
import PlutusTx.Maybe (Maybe (..))

-- While these types should be stable, we really don't want them changing,
-- so index them explicitly to be sure.
$(makeIsDataSchemaIndexed ''Bool [('False, 0), ('True, 1)])
$(makeIsDataSchemaIndexed ''Maybe [('Just, 0), ('Nothing, 1)])
$(makeIsDataSchemaIndexed ''Either [('Left, 0), ('Right, 1)])

-- Okay to use unstableMakeIsData here since there's only one alternative
-- and we're sure that will never change.
$(unstableMakeIsDataSchema ''())
$(unstableMakeIsDataSchema ''(,))
$(unstableMakeIsDataSchema ''(,,))
$(unstableMakeIsDataSchema ''(,,,))
