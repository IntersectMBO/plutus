{-# LANGUAGE TemplateHaskell #-}

module Playground.TH
  ( mkFunction
  ) where

import           Data.Proxy          (Proxy (Proxy))
import           Data.Swagger.Schema (toInlinedSchema)
import           Data.Text           (pack)
import           Language.Haskell.TH (Body (NormalB), Clause (Clause), Dec (FunD), Exp, Info (VarI), Name, Q,
                                      Type (AppT, ArrowT, ConT, ForallT, TupleT, VarT), mkName, nameBase, reify)
import           Playground.API      (Fn (Fn), FunctionSchema (FunctionSchema))

mkFunction :: Name -> Q [Dec]
mkFunction name = do
  let newName = mkName $ nameBase name ++ "Schema"
      fn = Fn . pack $ nameBase name
  expression <- mkFunctionExp name fn
  pure [FunD newName [Clause [] (NormalB expression) []]]

{-# ANN mkFunctionExp ("HLint: ignore" :: String) #-}

mkFunctionExp :: Name -> Fn -> Q Exp
mkFunctionExp name fn = do
  r <- reify name
  case r of
    (VarI _ as _) ->
      let ts = args as
       in toSchemas fn ts
    _ -> error "Incorrect Name type provided to mkFunction"

toSchemas :: Fn -> [Type] -> Q Exp
toSchemas fn ts = do
  es <-
    foldr
      (\t e -> [|toInlinedSchema (Proxy :: Proxy $(pure t)) : $e|])
      [|[]|]
      ts
  [|FunctionSchema fn $(pure es)|]

{-# ANN args ("HLint: ignore" :: String) #-}

args :: Type -> [Type]
args (AppT (AppT ArrowT t1) as) = t1 : args as
args (ForallT _ _ as)           = args as
args (ConT _)                   = []
args (TupleT _)                 = []
args (AppT (VarT _) t)          = args t
args a                          = error $ "incorrect type in template haskell function: " ++ show a
