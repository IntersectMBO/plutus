-- | Functions related to @integer@.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module PlutusCore.StdLib.Data.Integer
    ( integer
    , succInteger
    ) where

import           PlutusCore.Core
import           PlutusCore.Default.Builtins
import           PlutusCore.MkPlc
import           PlutusCore.Name
import           PlutusCore.Quote
import           PlutusCore.Universe

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
