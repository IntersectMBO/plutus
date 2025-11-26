{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Functions related to @integer@.
module PlutusCore.StdLib.Data.Integer
  ( integer
  , succInteger
  ) where

import PlutusCore.Core
import PlutusCore.Default.Builtins
import PlutusCore.MkPlc
import PlutusCore.Name.Unique
import PlutusCore.Quote

integer :: uni `HasTypeLevel` Integer => Type tyname uni ()
integer = mkTyBuiltin @_ @Integer ()

{-|  @succ :: Integer -> Integer@ as a PLC term.

> \(i : integer) -> addInteger i 1 -}
succInteger
  :: (TermLike term tyname Name uni DefaultFun, uni `HasTypeAndTermLevel` Integer) => term ()
succInteger = runQuote $ do
  i <- freshName "i"
  return
    . lamAbs () i integer
    . mkIterAppNoAnn (builtin () AddInteger)
    $ [ var () i
      , mkConstant @Integer () 1
      ]
