{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}

module PlutusBenchmark.Ed25519.Compiled
  ( checkValidCompiled
  , msgAsData
  , signatureAsData
  , pkAsData
  ) where

import PlutusBenchmark.Ed25519 (checkValid)
import PlutusTx.Code (CompiledCode)
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.Plugin ()
import PlutusTx.Prelude
import PlutusTx.TH (compile)

checkValidCompiled
  :: CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> Bool)
checkValidCompiled =
  $$( compile
        [||
        \signature msg pk ->
          checkValid
            (unsafeFromBuiltinData signature)
            (unsafeFromBuiltinData msg)
            (unsafeFromBuiltinData pk)
        ||]
    )

msgAsData :: CompiledCode BuiltinData
msgAsData =
  liftCodeDef
    $ toBuiltinData @BuiltinByteString
      "\x68\x65\x6C\x6C\x6F\x20\x77\x6F\x72\x6C\x64"

signatureAsData :: CompiledCode BuiltinData
signatureAsData =
  $$( compile
        [||
        toBuiltinData @BuiltinByteString
          "\xC0\x80\xC2\x93\x21\x78\xC2\xAD\xC2\xA7\xC3\x91\x7A\x60\x09\xC3\xB3\
          \\x7C\xC3\x83\x24\x58\x24\xC3\xA9\xC2\xA6\xC3\xAA\xC0\x80\xC2\x86\xC2\
          \\x98\x6C\x14\xC3\xB3\x34\xC3\x99\x15\xC2\x98\xC2\xB4\x7B\x24\x4D\xC3\
          \\xA3\x52\xC3\x96\xC3\x9A\x25\xC3\xB1\xC2\x9D\x05\x0E\x05\x09\xC2\x98\
          \\xC2\x8C\xC2\xAB\xC3\xB0\xC3\x88\x66\xC2\xB8\xC2\x85\xC3\x8B\xC3\xA3\
          \\x7A\xC2\xA3\xC0\x80\xC2\xB9\xC2\x9B\x59\xC2\x8B\xC2\xB2\xC3\xB9\x02"
        ||]
    )

pkAsData :: CompiledCode BuiltinData
pkAsData =
  liftCodeDef
    $ toBuiltinData @BuiltinByteString
      "\x28\x3A\xC3\xBF\xC3\xBB\xC2\x81\x37\x2D\x5E\x77\xC3\xBD\xC2\x91\x0B\x68\
      \\x1B\xC2\xAB\x72\xC2\xBD\xC3\x9F\x2F\xC3\x95\x51\x7A\x62\xC3\xB9\xC2\xAF\
      \\x24\x7A\xC3\x93\x71\xC3\x83\x11\xC3\x86"
