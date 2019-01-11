{-# LANGUAGE TemplateHaskell #-}

module Playground.TH
    ( mkFunction
    , mkFunctions
    , mkSingleFunction
    ) where

import           Data.Proxy          (Proxy (Proxy))
import           Data.Swagger.Schema (toInlinedSchema)
import           Data.Text           (pack)
import           Language.Haskell.TH (Body (NormalB), Clause (Clause), Dec (FunD, ValD), Exp (ListE, VarE), Info (VarI),
                                      Name, Pat (VarP), Q, Type (AppT, ArrowT, ConT, ForallT, TupleT, VarT), mkName,
                                      nameBase, reify)
import           Playground.API      (Fn (Fn), FunctionSchema (FunctionSchema))

mkFunctions :: [Name] -> Q [Dec]
mkFunctions names = do
    fns <- traverse mkFunction' names
    let newNames = fmap mkNewName names
        schemas = ValD (VarP (mkName "schemas")) (NormalB (ListE newNames)) []
    pure $ fns <> [schemas]
  where
    mkNewName name = VarE . mkName $ nameBase name ++ "Schema"

{-# ANN mkFunction ("HLint: ignore" :: String) #-}
mkFunction :: Name -> Q [Dec]
mkFunction _ = error
  $ ""
  </> "mkFunction has been replaced by mkFunctions"
  </> " "
  </> "replace all calls to mkFunction with a single call to mkFunctions, e.g."
  </> " "
  </> " | $(mkFunction 'functionOne)"
  </> " | $(mkFunction 'functionTwo)"
  </> " "
  </> "becomes:"
  </> " "
  </> " | $(mkFunctions ['functionOne, 'functionTwo])"
  </> " "
  where
    a </> b = a <> "\n" <> b

mkSingleFunction :: Name -> Q [Dec]
mkSingleFunction name = do
  dec <- mkFunction' name
  pure [dec]

mkFunction' :: Name -> Q Dec
mkFunction' name = do
    let newName = mkName $ nameBase name ++ "Schema"
        fn = Fn . pack $ nameBase name
    expression <- mkFunctionExp name fn
    pure $ FunD newName [Clause [] (NormalB expression) []]

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
args (AppT (ConT _) _)          = []
args (ForallT _ _ as)           = args as
args (ConT _)                   = []
args (TupleT _)                 = []
args (AppT (VarT _) t)          = args t
args a                          = error $ "incorrect type in template haskell function: " ++ show a
