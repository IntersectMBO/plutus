{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

module Playground.TH where

import           Data.Proxy
import           Data.Swagger.Schema (ToSchema, toInlinedSchema)
import           Data.Text           (pack)
import           Language.Haskell.TH
import           Playground.API      (Fn (Fn), FunctionSchema (FunctionSchema))

mkFunction :: Name -> Q [Dec]
mkFunction name = do
  let newName = mkName $ nameBase name ++ "Schema"
      fn = Fn . pack $ nameBase name
  exp <- mkFunction' name fn
  pure [FunD newName [Clause [] (NormalB exp) []]]

{-# ANN module ("HLint: ignore" :: String) #-}

mkFunction' :: Name -> Fn -> Q Exp
mkFunction' name fn = do
  let newName = mkName $ (nameBase name) ++ "Schema"
  r <- reify name
  case r of
    (VarI _ as _) ->
      let ts = args as
       in toSchemas fn ts
    _ -> error "unknown"

toSchemas :: Fn -> [Type] -> Q Exp
toSchemas fn ts = do
  es <-
    foldr
      (\t e -> [|$e ++ [toInlinedSchema (Proxy :: Proxy $(pure t))]|])
      [|[]|]
      ts
  [|FunctionSchema fn $(pure es)|]

args (AppT (AppT ArrowT t1) as) = t1 : args as
args (ForallT _ _ as)           = args as
args (ConT _)                   = []
args (AppT (VarT v) t)          = []
args a                          = error $ "incorrect type " ++ show a
