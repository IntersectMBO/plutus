{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
module Lib where

import           Common
import           PlcTestUtils

import           Language.Haskell.TH
import           Language.PlutusTx.Prelude

import qualified Language.PlutusTx.Builtins   as Builtins
import           Language.PlutusTx.Code
import           Language.PlutusTx.Evaluation
import           Language.PlutusTx.Prelude
import           Language.PlutusTx.TH

import           Language.PlutusCore.Pretty   (PrettyConst)
import qualified Language.PlutusCore.Universe as PLC
import qualified Language.UntypedPlutusCore   as UPLC

-- import           Codec.Serialise              (Serialise)
import           Data.Text.Prettyprint.Doc
import           Flat                         (Flat)

instance (PLC.Closed uni, uni `PLC.Everywhere` Flat, Flat fun) =>
            ToUPlc (CompiledCodeIn uni fun a) uni fun where
    toUPlc = catchAll . getPlc

goldenPir
    :: (PLC.GShow uni, PLC.Closed uni, uni `PLC.Everywhere` PrettyConst, uni `PLC.Everywhere` Flat, Pretty fun, Flat fun)
    => String -> CompiledCodeIn uni fun a -> TestNested
goldenPir name value = nestedGoldenVsDoc name $ pretty $ getPir value
