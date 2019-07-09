-- | Functions related to @integer@.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Language.PlutusCore.StdLib.Data.Integer
    ( succInteger
    ) where

import           Language.PlutusCore.Constant.Universe
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type

import           Data.Proxy

-- |  @succ :: Integer -> Integer@ as a PLC term.
--
-- > \(i : integer) -> addInteger i 1
succInteger :: forall term uni. (TermLike term TyName Name uni, uni `Includes` Integer) => term ()
succInteger = runQuote $ do
    i  <- freshName () "i"
    return
        . lamAbs () i (constantType @Integer Proxy ())
        . mkIterApp () (builtin () $ BuiltinName () AddInteger)
        $ [ var () i
          , constantTerm @Integer () 1
          ]
