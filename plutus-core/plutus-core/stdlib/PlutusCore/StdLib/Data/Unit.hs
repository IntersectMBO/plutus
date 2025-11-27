{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | @unit@ and related functions.
module PlutusCore.StdLib.Data.Unit
  ( unit
  , unitval
  , sequ
  ) where

import PlutusCore.Core
import PlutusCore.MkPlc
import PlutusCore.Name.Unique
import PlutusCore.Quote

-- | '()' as a PLC type.
unit :: uni `HasTypeLevel` () => Type tyname uni ()
unit = mkTyBuiltin @_ @() ()

-- | '()' as a PLC term.
unitval :: (TermLike term tyname name uni fun, uni `HasTermLevel` ()) => term ()
unitval = mkConstant () ()

-- | 'seq' specified to '()' as a PLC term.
sequ :: (TermLike term tyname Name uni fun, uni `HasTypeAndTermLevel` ()) => term ()
sequ = runQuote $ do
  x <- freshName "x"
  y <- freshName "y"
  return
    . lamAbs () x unit
    . lamAbs () y unit
    $ unitval
