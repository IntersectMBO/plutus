-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

module PlutusBenchmark.Ed25519.Compiled (
  checkValidCompiled,
  msgAsData,
  signatureAsData,
  pkAsData
  ) where

import PlutusBenchmark.Ed25519 (checkValid)
import PlutusTx.Code (CompiledCode)
import PlutusTx.IsData (toBuiltinData, unsafeFromBuiltinData)
import PlutusTx.Plugin ()
import PlutusTx.Prelude
import PlutusTx.TH (compile)

checkValidCompiled :: CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> Bool)
checkValidCompiled = $$(compile [|| \signature msg pk -> checkValid (unsafeFromBuiltinData signature)
                                                                    (unsafeFromBuiltinData msg)
                                                                    (unsafeFromBuiltinData pk) ||])

msgAsData :: CompiledCode BuiltinData
msgAsData = $$(compile [|| toBuiltinData ("hello world" :: BuiltinByteString) ||])

signatureAsData :: CompiledCode BuiltinData
signatureAsData =
  $$(compile [|| toBuiltinData ("\NUL\147!x\173\167\209z`\t\243|\195$X$\233\166\234\NUL\134\152l\DC4\243\&4\217\NAK\152\180{$M\227R\214\218%\241\157\ENQ\SO\ENQ\t\152\140\171\240\200f\184\133\203\227z\163\NUL\185\155Y\139\178\249\STX" :: BuiltinByteString) ||])

pkAsData :: CompiledCode BuiltinData
pkAsData =
  $$(compile [|| toBuiltinData ("(:\255\251\129\&7-^w\253\145\vh\ESC\171r\189\223/\213Qzb\249\175$z\211q\195\DC1\198" :: BuiltinByteString) ||])
