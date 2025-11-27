{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-full-laziness #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-unbox-small-strict-fields #-}
{-# OPTIONS_GHC -fno-unbox-strict-fields #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.1.0 #-}

module ByteStringLiterals.Lib where

import PlutusTx.Builtins (BuiltinByteStringHex (..))

{-

PlutusTx.Builtins.HasOpaque.stringToBuiltinByteStringHex
  (GHC.Types.:
    @GHC.Types.Char
    (GHC.Types.C# 'f'#)
    (GHC.Base.build
        @GHC.Types.Char
        (\ (@b) -> GHC.CString.unpackFoldrCString# @b "0d1"#)))
-}
{-# INLINEABLE hex #-}
hex :: BuiltinByteStringHex
hex = "f0d1"
