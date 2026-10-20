{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}

module BuiltinCasing.TargetVersion.Lib where

import PlutusTx.IsData (makeIsDataIndexed)

data AB = A | B

makeIsDataIndexed ''AB [('A, 0), ('B, 1)]
