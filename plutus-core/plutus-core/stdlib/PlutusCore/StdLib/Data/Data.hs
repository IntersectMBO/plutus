-- editorconfig-checker-disable-file
-- | Built-in @pair@ and related functions.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module PlutusCore.StdLib.Data.Data
    ( dataTy
    , matchData
    ) where

import Prelude hiding (uncurry)

import PlutusCore.Core
import PlutusCore.Data
import PlutusCore.Default
import PlutusCore.MkPlc
import PlutusCore.Name.Unique
import PlutusCore.Quote

import PlutusCore.StdLib.Data.Integer
import PlutusCore.StdLib.Data.MatchOption

import Data.ByteString (ByteString)

-- | @Data@ as a built-in PLC type.
dataTy :: uni `HasTypeLevel` Data => Type tyname uni ()
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
-- >           matchData
-- >               {r}
-- >               fConstr
-- >               fMap
-- >               fList
-- >               fI
-- >               fB
-- >               d
matchData :: TermLike term TyName Name DefaultUni DefaultFun => MatchOption -> term ()
matchData optMatch = runQuote $ do
    r       <- freshTyName "r"
    fConstr <- freshName "fConstr"
    fMap    <- freshName "fMap"
    fList   <- freshName "fList"
    fI      <- freshName "fI"
    fB      <- freshName "fB"
    d       <- freshName "d"
    let listData = mkTyBuiltin @_ @[Data] ()
        listPairData = mkTyBuiltin @_ @[(Data, Data)] ()
        bytestring = mkTyBuiltin @_ @ByteString ()
    return
        . lamAbs () d dataTy
        . tyAbs () r (Type ())
        . lamAbs () fConstr (TyFun () integer . TyFun () listData $ TyVar () r)
        . lamAbs () fMap (TyFun () listPairData $ TyVar () r)
        . lamAbs () fList (TyFun () listData $ TyVar () r)
        . lamAbs () fI (TyFun () integer $ TyVar () r)
        . lamAbs () fB (TyFun () bytestring $ TyVar () r)
        $ mkIterAppNoAnn (tyInst () (builtin () CaseData) $ TyVar () r)
            [ var () fConstr
            , var () fMap
            , var () fList
            , var () fI
            , var () fB
            , var () d
            ]
