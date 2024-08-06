-- editorconfig-checker-disable-file
-- | Built-in @pair@ and related functions.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module PlutusCore.StdLib.Data.Data
    ( dataTy
    , caseData
    ) where

import Prelude hiding (uncurry)

import PlutusCore.Core
import PlutusCore.Data
import PlutusCore.Default
import PlutusCore.MkPlc
import PlutusCore.Name.Unique
import PlutusCore.Quote

-- | @Data@ as a built-in PLC type.
dataTy :: uni `HasTypeLevel` Data => Type tyname uni ()
dataTy = mkTyBuiltin @_ @Data ()

-- | Pattern matching over 'Data' inside PLC.
--
-- > \(d : data) -> /\(r :: *) -> caseData {r} d
caseData :: TermLike term TyName Name DefaultUni DefaultFun => term ()
caseData = runQuote $ do
    r <- freshTyName "r"
    d <- freshName "d"
    return
        . lamAbs () d dataTy
        . tyAbs () r (Type ())
        . apply () (tyInst () (builtin () CaseData) $ TyVar () r)
        $ var () d
