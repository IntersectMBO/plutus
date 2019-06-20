{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Plugin.Lib where

import           Common
import           PlcTestUtils

import           Language.Haskell.TH
import           Language.PlutusTx.Prelude

import qualified Language.PlutusTx.Builtins   as Builtins
import           Language.PlutusTx.Code
import           Language.PlutusTx.Evaluation
import           Language.PlutusTx.Prelude
import           Language.PlutusTx.TH

import           Data.Text.Prettyprint.Doc

{-# ANN module "HLint: ignore" #-}

instance GetProgram (CompiledCode a) where
    getProgram = catchAll . getPlc

goldenPir :: String -> CompiledCode a -> TestNested
goldenPir name value = nestedGoldenVsDoc name $ pretty $ getPir value


-- This is here for the Plugin spec, but we're testing using things from a different module
andExternal :: Bool -> Bool -> Bool
andExternal a b = if a then b else False

data MyExternalRecord = MyExternalRecord { myExternal :: Integer }

{-# INLINABLE evenDirect #-}
evenDirect :: Integer -> Bool
evenDirect n = if Builtins.equalsInteger n 0 then True else oddDirect (Builtins.subtractInteger n 1)

{-# INLINABLE oddDirect #-}
oddDirect :: Integer -> Bool
oddDirect n = if Builtins.equalsInteger n 0 then False else evenDirect (Builtins.subtractInteger n 1)

-- GHC will lift out the error call to the top level, which is unsafe unless we bind it lazily.
-- This is in Lib so we get the fully optimized unfolding with awkward top-level binds and everything.
joinError :: Bool -> Bool -> ()
joinError x y = if andExternal x y then Builtins.error () else ()
