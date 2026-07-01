-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE PackageImports        #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ViewPatterns          #-}

-- Comment out in order to reproduce the compilation issue.
-- WATCH OUT: THIS IS PROBABLY GOING TO OOO YOUR MACHINE
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=1 #-}

module Main where

import PlutusTx qualified
import PlutusTx.Prelude hiding (Semigroup (..), unless)
import Prelude qualified as H

main :: H.IO ()
main = do
  H.pure ()

data C = A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | Q | R

PlutusTx.makeIsDataIndexed ''C [ ('A, 0) , ('B, 1) , ('C, 2) , ('D, 3) , ('E, 4) , ('F, 5) , ('G, 6) , ('H, 7) , ('I, 8) , ('J, 9) , ('K, 10) , ('L, 11) , ('M, 12) , ('N, 13) , ('O, 14) , ('P, 15) , ('Q, 16) , ('R, 17) ]

{-# INLINABLE validator #-}
validator ::
  BuiltinData
  -> BuiltinData
  -> BuiltinData
  -> Bool
validator d _ _ =
  let !_ = PlutusTx.unsafeFromBuiltinData @C d
   in True

unappliedValidator ::
  PlutusTx.CompiledCode (PlutusTx.BuiltinData -> PlutusTx.BuiltinData -> PlutusTx.BuiltinData -> BuiltinUnit)
unappliedValidator =
   $$(PlutusTx.compile [|| \d r c -> check $ validator d r c ||])

