{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}

module ByteStringLiterals.Lib where

import PlutusTx.Builtins (BuiltinByteStringHex (..))

{-# INLINEABLE hex #-}
hex :: BuiltinByteStringHex
hex = "f0"
