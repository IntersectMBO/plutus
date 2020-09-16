-- | @unit@ and related functions.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Language.PlutusCore.StdLib.Data.Unit
    ( unit
    , unitval
    , sequ
    ) where

import           Language.PlutusCore.Core
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Universe
import           Language.PlutusCore.Quote

-- | '()' as a PLC type.
unit :: uni `Includes` () => Type TyName uni ()
unit = mkTyBuiltin @() ()

-- | '()' as a PLC term.
unitval :: (TermLike term TyName Name uni fun, uni `Includes` ()) => term ()
unitval = mkConstant () ()

-- | 'seq' specified to '()' as a PLC term.
sequ :: (TermLike term TyName Name uni fun, uni `Includes` ()) => term ()
sequ = runQuote $ do
    x <- freshName "x"
    y <- freshName "y"
    return
        . lamAbs () x unit
        . lamAbs () y unit
        $ unitval
