{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -fwarn-missing-signatures     #-}
{-# OPTIONS_GHC -fno-warn-unused-imports      #-}

{-# OPTIONS_GHC -fexpose-all-unfoldings       #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr              #-}
{-# OPTIONS_GHC -fno-strictness               #-}
{-# OPTIONS_GHC -fno-worker-wrapper           #-}

module Main where

import           Control.Monad
import           System.Environment

import           Control.Monad                                              ()
import           Language.PlutusCore.Constant                               (DynamicBuiltinNameMeanings (..))
import           Language.PlutusCore.Evaluation.Machine.Cek                 ()
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import qualified Language.PlutusCore.Pretty                                 as PLC
import qualified Language.PlutusTx                                          as Tx
import           Language.PlutusTx.Prelude                                  as TxPrelude hiding (replicate)
import           Language.UntypedPlutusCore
import           Language.UntypedPlutusCore.Evaluation.Machine.Cek
import           Plutus.Benchmark.Clausify                                  (Formula (..), clauses, replicate)
import qualified Data.Map as Map

{-# INLINABLE formula1 #-}  -- Overflow
formula1 :: Formula  -- (a = a = a) = (a = a = a) = (a = a = a)
formula1 = Eqv (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))
               (Eqv (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))
                    (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1))))

{-# INLINABLE formula2 #-} -- Overflow
formula2 :: Formula -- (a = b = c) = (d = e = f) = (g = h = i)
formula2 = Eqv (Eqv (Sym 1) (Eqv (Sym 2) (Sym 3)))
               (Eqv (Eqv (Sym 4) (Eqv (Sym 5) (Sym 6)))
                    (Eqv (Sym 7) (Eqv (Sym 8) (Sym 9))))

{-# INLINABLE formula3 #-}
formula3 :: Formula  -- (a = a = a) = (a = a = a)
formula3 = Eqv (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))
               (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))

{-# INLINABLE formula4 #-} -- One execution takes about 0.35s and 300 MB
formula4 :: Formula  -- (a = a) = (a = a) = (a = a)
formula4 = Eqv (Eqv (Sym 1) (Sym 1))
               (Eqv (Eqv (Sym 1) (Sym 1))
                    (Eqv (Sym 1) (Sym 1)))

{-# INLINABLE formula5 #-}  -- One execution takes about 1.5s and 660 MB
formula5 :: Formula  -- (a = a = a) = (a = a) = (a = a)
formula5 = Eqv (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))
               (Eqv (Eqv (Sym 1) (Sym 1))
                    (Eqv (Sym 1) (Sym 1)))

{-# INLINABLE formula5a #-}  -- One execution takes about 2s and 1 GB
formula5a :: Formula  -- (a = b = c) = (d = e) = (f = g)
formula5a = Eqv (Eqv (Sym 1) (Eqv (Sym 2) (Sym 3)))
               (Eqv (Eqv (Sym 4) (Sym 5))
                    (Eqv (Sym 6) (Sym 7)))

{-# INLINABLE formula6 #-}  -- One execution takes about 11s and 5 GB
formula6 :: Formula  -- (a = a = a) = (a = a = a) = (a = a)
formula6 = Eqv (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))
               (Eqv (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))
                    (Eqv (Sym 1) (Sym 1)))


count :: Integer
count = 1

main :: IO ()
main = do
  let (Program _ _ code) = Tx.getPlc $ $$(Tx.compile [|| map clauses (replicate count formula5a)  ||])
      result = unsafeEvaluateCek (DynamicBuiltinNameMeanings Map.empty) defaultCostModel code
  print . PLC.prettyPlcClassicDebug $ result
