-- | Functions related to @integer@.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Language.PlutusCore.StdLib.Data.Integer
    ( integer
    , succInteger
    ) where

import           Language.PlutusCore.Builtins
import           Language.PlutusCore.Core
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Universe

integer :: uni `Includes` Integer => Type tyname uni ()
integer = mkTyBuiltin @Integer ()

-- |  @succ :: Integer -> Integer@ as a PLC term.
--
-- > \(i : integer) -> addInteger i 1
succInteger :: (TermLike term TyName Name uni DefaultFun, uni `Includes` Integer) => term ()
succInteger = runQuote $ do
    i  <- freshName "i"
    return
        . lamAbs () i integer
        . mkIterApp () (builtin () AddInteger)
        $ [ var () i
          , mkConstant @Integer () 1
          ]
