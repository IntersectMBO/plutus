{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -Wno-orphans  #-}
module Lib where

import           Common
import           PlcTestUtils

import           PlutusTx.Code

import qualified PlutusCore        as PLC
import           PlutusCore.Pretty (PrettyConst)

import           Flat              (Flat)
import           Prettyprinter

instance (PLC.Closed uni, uni `PLC.Everywhere` Flat, uni `PLC.Everywhere` PrettyConst, PLC.GShow uni, Pretty fun, Flat fun) =>
            ToUPlc (CompiledCodeIn uni fun a) uni fun where
    toUPlc v = do
        v' <- catchAll $ getPlc v
        toUPlc v'

goldenPir
    :: (PLC.Closed uni, uni `PLC.Everywhere` PrettyConst, uni `PLC.Everywhere` Flat, PLC.GShow uni, Pretty fun, Flat fun)
    => String -> CompiledCodeIn uni fun a -> TestNested
goldenPir name value = nestedGoldenVsDoc name $ pretty $ getPir value
