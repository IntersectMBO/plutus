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
import PlutusCore.Name
import PlutusCore.Quote

import Data.ByteString (ByteString)
import PlutusCore.StdLib.Data.Integer
import PlutusCore.StdLib.Data.Unit

-- | @Data@ as a built-in PLC type.
dataTy :: uni `Contains` Data => Type TyName uni ()
dataTy = mkTyBuiltin @_ @Data ()

-- | Pattern matching over 'Data' inside PLC.
--
-- > \(d : data) ->
-- >     /\(r :: *) ->
-- >      \(fConstr : integer -> list data -> r)
-- >       (fMap : list (pair data data) -> r)
-- >       (fList : list data -> r)
-- >       (fI : integer -> r)
-- >       (fB : bytestring -> r) ->
-- >           caseData
-- >               {unit -> r}
-- >               d
-- >               (\(i : integer) (ds : list data) (u : unit) -> fConstr i ds)
-- >               (\(es : list (pair data data)) (u : unit) -> fMap es)
-- >               (\(ds : list data) (u : unit) -> fList ds)
-- >               (\(i : integer) (u : unit) -> fI i)
-- >               (\(b : bytestring) (u : unit) -> fB b)
-- >               unitval
caseData :: TermLike term TyName Name DefaultUni DefaultFun => term ()
caseData = runQuote $ do
    r       <- freshTyName "r"
    fConstr <- freshName "fConstr"
    fMap    <- freshName "fMap"
    fList   <- freshName "fList"
    fI      <- freshName "fI"
    fB      <- freshName "fB"
    d       <- freshName "d"
    i       <- freshName "i"
    ds      <- freshName "ds"
    es      <- freshName "es"
    b       <- freshName "b"
    u       <- freshName "u"
    let bytestring   = mkTyBuiltin @_ @ByteString ()
        listData     = mkTyBuiltin @_ @[Data] ()
        listPairData = mkTyBuiltin @_ @[(Data, Data)] ()
    return
        . lamAbs () d dataTy
        . tyAbs () r (Type ())
        . lamAbs () fConstr (TyFun () integer . TyFun () listData $ TyVar () r)
        . lamAbs () fMap (TyFun () listPairData $ TyVar () r)
        . lamAbs () fList (TyFun () listData $ TyVar () r)
        . lamAbs () fI (TyFun () integer $ TyVar () r)
        . lamAbs () fB (TyFun () bytestring $ TyVar () r)
        $ mkIterApp () (tyInst () (builtin () CaseData) . TyFun () unit $ TyVar () r)
            [ var () d
            , lamAbs () i integer . lamAbs () ds listData . lamAbs () u unit $
                mkIterApp () (var () fConstr) [ var () i, var () ds]
            , lamAbs () es listPairData . lamAbs () u unit . apply () (var () fMap) $ var () es
            , lamAbs () ds listData . lamAbs () u unit . apply () (var () fList) $ var () ds
            , lamAbs () i integer . lamAbs () u unit . apply () (var () fI) $ var () i
            , lamAbs () b bytestring . lamAbs () u unit . apply () (var () fB) $ var () b
            , unitval
            ]
