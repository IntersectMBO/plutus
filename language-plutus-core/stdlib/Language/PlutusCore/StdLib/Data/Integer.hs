-- | Functions related to @integer@.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Language.PlutusCore.StdLib.Data.Integer
    ( succInteger
    ) where

import           Language.PlutusCore.Constant.Make
import           Language.PlutusCore.Constant.Universe
import           Language.PlutusCore.Core
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote

-- |  @succ :: Integer -> Integer@ as a PLC term.
--
-- > \(i : integer) -> addInteger i 1
succInteger :: (TermLike term TyName Name uni, uni `Includes` Integer) => term ()
succInteger = runQuote $ do
    i  <- freshName () "i"
    return
        . lamAbs () i (makeTyBuiltin @Integer)
        . mkIterApp () (builtin () $ BuiltinName () AddInteger)
        $ [ var () i
          , makeConstant @Integer 1
          ]
