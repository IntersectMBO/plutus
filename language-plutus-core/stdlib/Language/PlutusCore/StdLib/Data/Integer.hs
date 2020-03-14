-- | Functions related to @integer@.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Language.PlutusCore.StdLib.Data.Integer
    ( succInteger
    ) where

import           Language.PlutusCore.Core
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Universe

-- |  @succ :: Integer -> Integer@ as a PLC term.
--
-- > \(i : integer) -> addInteger i 1
succInteger :: (TermLike term TyName Name uni, uni `Includes` Integer) => term ()
succInteger = runQuote $ do
    i  <- freshName () "i"
    return
        . lamAbs () i (mkTyBuiltin @Integer ())
        . mkIterApp () (builtin () $ BuiltinName () AddInteger)
        $ [ var () i
          , mkConstant @Integer () 1
          ]
