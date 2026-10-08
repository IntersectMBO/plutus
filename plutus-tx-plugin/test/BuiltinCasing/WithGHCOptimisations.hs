{-# OPTIONS_GHC -O1 -ffull-laziness #-}

module BuiltinCasing.WithGHCOptimisations where

import PlutusTx.Builtins (BuiltinData, caseData, caseInteger)

selectIntegerBranch :: Integer -> Integer
selectIntegerBranch index = caseInteger index [10, 20, 30]

selectDataBranch :: BuiltinData -> Integer
selectDataBranch datum = caseData datum [\_ -> 10, \_ -> 20, \_ -> 30]
