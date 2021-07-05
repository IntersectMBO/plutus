{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module PlutusCore.Examples.Data.Data
    ( ofoldrData
    ) where

import           PlutusCore.Core
import           PlutusCore.Data
import           PlutusCore.Default
import           PlutusCore.MkPlc
import           PlutusCore.Name
import           PlutusCore.Quote

import           PlutusCore.StdLib.Data.Data
import           PlutusCore.StdLib.Data.Function
import           PlutusCore.StdLib.Data.Integer
import           PlutusCore.StdLib.Data.List
import           PlutusCore.StdLib.Data.Pair

import           PlutusCore.Examples.Builtins
import           PlutusCore.Examples.Data.List
import           PlutusCore.Examples.Data.Pair

import           Data.ByteString                 (ByteString)

-- | Right-folding over 'Data' inside PLC currently hardcoded to only ever return @Data@ as a
-- result, 'cause we need to be able to map built-in lists and pairs in the definition of the
-- right fold for 'Data' and we can only do that monomorphically
-- (see Note [Representable built-in functions over polymorphic built-in types]),
-- which forces us to always return a 'Data'.
-- Alternatively we could convert built-in lists and pairs to their non-built-in
-- Scott/Church-encoded forms, map polymorphically and convert back at the call site, but we really
-- only use this definition as a test, so it's fine to make it overly specific for the sake of
-- keeping the actual test trivial.
--
-- > metaTypeLet r = data in
-- >     \(fConstr : integer -> list r -> r)
-- >      (fMap : list (pair r r) -> r)
-- >      (fList : list r -> r)
-- >      (fI : integer -> r)
-- >      (fB : bytestring -> r) ->
-- >          fix {data} {r} \(rec : data -> r) (d : data) ->
-- >              caseData
-- >                  d
-- >                  {r}
-- >                  (\(i : integer) (ds : list data) -> fConstr i (omapList {data} rec ds)
-- >                  (\(es : list (pair data data)) ->
-- >                      fMap (omapList {pair data data} (obothPair {data} rec) es))
-- >                  (\(ds : list data) -> fList (omapList {data} rec ds))
-- >                  fI
-- >                  fB
ofoldrData :: Term TyName Name DefaultUni (Either DefaultFun ExtensionFun) ()
ofoldrData = runQuote $ do
    let r = dataTy
    fConstr <- freshName "fConstr"
    fMap    <- freshName "fMap"
    fList   <- freshName "fList"
    fI      <- freshName "fI"
    fB      <- freshName "fB"
    rec     <- freshName "rec"
    d       <- freshName "d"
    i       <- freshName "i"
    ds      <- freshName "ds"
    es      <- freshName "es"
    let listData = mkTyBuiltin @_ @[Data] ()
        listR = TyApp () list r
        opair a = mkIterTyApp () pair [a, a]
        unwrap' ann = apply ann $ mapFun Left caseData
    return
        . lamAbs () fConstr (TyFun () integer $ TyFun () listR r)
        . lamAbs () fMap (TyFun () (TyApp () list $ opair r) r)
        . lamAbs () fList (TyFun () listR r)
        . lamAbs () fI (TyFun () integer r)
        . lamAbs () fB (TyFun () (mkTyBuiltin @_ @ByteString ()) r)
        . apply () (mkIterInst () fix [dataTy, r])
        . lamAbs () rec (TyFun () dataTy r)
        . lamAbs () d dataTy
        $ mkIterApp () (tyInst () (unwrap' () (var () d)) r)
            [   lamAbs () i integer
              . lamAbs () ds listData
              $ mkIterApp () (var () fConstr)
                  [ var () i
                  , mkIterApp () (tyInst () omapList dataTy) [var () rec, var () ds]
                  ]
            ,   lamAbs () es (TyApp () list $ opair dataTy)
              . apply () (var () fMap)
              $ mkIterApp () (tyInst () omapList $ opair dataTy)
                  [ apply () (tyInst () obothPair dataTy) $ var () rec
                  , var () es
                  ]
            ,   lamAbs () ds listData
              . apply () (var () fList)
              $ mkIterApp () (tyInst () omapList dataTy)
                  [ var () rec
                  , var () ds
                  ]
            , var () fI
            , var () fB
            ]
