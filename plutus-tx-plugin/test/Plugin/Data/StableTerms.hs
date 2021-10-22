{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-context #-}
-- We don't truncate types for terms that are compiled separately, to be applied afterward in other test cases.
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-truncate-types #-}

module Plugin.Data.StableTerms where

import           Data.Proxy      (Proxy (..))
import           PlutusTx.Code   (CompiledCode)
import           PlutusTx.Plugin (plc)

stableListConstruct :: CompiledCode [Integer]
stableListConstruct = plc (Proxy @"stableListConstruct") ([]::[Integer])

stableTrue :: CompiledCode Bool
stableTrue = plc (Proxy @"stableTrue") True

stableFalse :: CompiledCode Bool
stableFalse = plc (Proxy @"stableFalse") False
