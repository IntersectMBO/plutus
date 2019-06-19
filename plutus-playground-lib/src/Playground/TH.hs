{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE TemplateHaskell #-}

module Playground.TH
    ( mkKnownCurrencies
    ) where

import           Data.Proxy          (Proxy (Proxy))
import           Data.Text           (pack)
import           Language.Haskell.TH (Body (NormalB), Clause (Clause), Dec (FunD, SigD, ValD), Exp (ListE, VarE),
                                      Info (VarI), Name, Pat (VarP), Q,
                                      Type (AppT, ArrowT, ConT, ForallT, ListT, TupleT, VarT), mkName, nameBase, reify)
import           Playground.API      (Fn (Fn), FunctionSchema (FunctionSchema), adaCurrency)

-- TODO: add a type declaration to registeredKnownCurrencies
mkKnownCurrencies :: [Name] -> Q [Dec]
mkKnownCurrencies ks = do
    let name = mkName "registeredKnownCurrencies"
        names = fmap VarE ('Playground.API.adaCurrency : ks)
        body = NormalB (ListE names)
        val = ValD (VarP name) body []
        typeName = mkName "KnownCurrency"
        sig = SigD name (AppT ListT (ConT typeName))
    pure [sig, val]
