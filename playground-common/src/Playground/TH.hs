{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE DeriveAnyClass   #-}
{-# LANGUAGE DeriveGeneric    #-}
{-# LANGUAGE KindSignatures   #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module Playground.TH
    ( mkFunction
    , mkFunctions
    , mkIotsDefinitions
    , ensureKnownCurrencies
    , ensureIotsDefinitions
    , mkSchemaDefinitions
    , mkSingleFunction
    , mkKnownCurrencies
    ) where

import           Data.Row                 (type (.\\))
import           Data.Text                (pack)
import           IOTS                     (HList (HCons, HNil), Tagged (Tagged))
import qualified IOTS
import           Language.Haskell.TH      (Body (NormalB), Clause (Clause), Dec (FunD, SigD, TySynD, ValD),
                                           Exp (ListE, LitE, VarE), Info (TyConI, VarI), Lit (StringL), Name,
                                           Pat (VarP), Q, Type (AppT, ArrowT, ConT, ForallT, ListT, TupleT, VarT),
                                           appTypeE, conE, litT, lookupValueName, mkName, nameBase, normalB, reify,
                                           sigD, strTyLit, valD, varE, varP)
import           Language.Plutus.Contract (BlockchainActions)
import           Playground.Schema        (endpointsToSchemas)
import           Playground.Types         (EndpointName (EndpointName), FunctionSchema (FunctionSchema), adaCurrency)
import           Schema                   (FormSchema, toSchema)

mkFunctions :: [Name] -> Q [Dec]
mkFunctions names = do
    fns <- traverse mkFunction' names
    let newNames = fmap mkNewName names
        schemas = ValD (VarP (mkName "schemas")) (NormalB (ListE newNames)) []
    pure $ fns <> [schemas]
  where
    mkNewName name = VarE . mkName $ nameBase name ++ "Schema"

registeredKnownCurrenciesBindingName :: String
registeredKnownCurrenciesBindingName = "registeredKnownCurrencies"

iotsBindingName :: String
iotsBindingName = "iotsDefinitions"

mkIotsDefinitions :: [Name] -> Q [Dec]
mkIotsDefinitions names = do
    iotsDefinition <- [|IOTS.export $(mkTaggedList names)|]
    pure [ValD (VarP (mkName iotsBindingName)) (NormalB iotsDefinition) []]

unlessBound :: String -> (Name -> Q [Dec]) -> Q [Dec]
unlessBound bindingName definition = do
    bound <- lookupValueName bindingName
    case bound of
        Just _  -> pure []
        Nothing -> definition $ mkName bindingName

ensureIotsDefinitions :: Q [Dec]
ensureIotsDefinitions =
    unlessBound iotsBindingName $ \name ->
        pure [ValD (VarP name) (NormalB (LitE (StringL ""))) []]

ensureKnownCurrencies :: Q [Dec]
ensureKnownCurrencies =
    unlessBound registeredKnownCurrenciesBindingName $ \_ ->
        mkKnownCurrencies []

schemaBindingName :: String
schemaBindingName = "schemas"

{-# ANN mkSchemaDefinitions
          ("HLint: ignore Redundant bracket" :: String)
        #-}

mkSchemaDefinitions :: Name -> Q [Dec]
mkSchemaDefinitions ts = do
    info <- reify ts
    case info of
        TyConI (TySynD _ [] t) -> do
            schemas <- [|endpointsToSchemas @($(pure t) .\\ BlockchainActions)|]
            unlessBound schemaBindingName $ \name -> do
                sig <- sigD name [t|[FunctionSchema FormSchema]|]
                body <- valD (varP name) (normalB (pure schemas)) []
                pure [sig, body]
        other ->
            error $
            "Incorrect Name type provided to mkSchemaDefinitions. Got: " <>
            show other

mkTaggedList :: [Name] -> Q Exp
mkTaggedList [] = [|HNil|]
mkTaggedList (x:xs) =
    let nameTag = appTypeE (conE 'Tagged) (litT (strTyLit (nameBase x)))
     in [|HCons ($nameTag $(varE x)) $(mkTaggedList xs)|]

{-# ANN mkFunction ("HLint: ignore" :: String) #-}

mkFunction :: Name -> Q [Dec]
mkFunction _ =
    error $
    "" </> "mkFunction has been replaced by mkFunctions" </> " " </>
    "replace all calls to mkFunction with a single call to mkFunctions, e.g." </>
    " " </>
    " | $(mkFunction 'functionOne)" </>
    " | $(mkFunction 'functionTwo)" </>
    " " </>
    "becomes:" </>
    " " </>
    " | $(mkFunctions ['functionOne, 'functionTwo])" </>
    " "
  where
    a </> b = a <> "\n" <> b

mkSingleFunction :: Name -> Q [Dec]
mkSingleFunction name = do
    dec <- mkFunction' name
    pure [dec]

mkFunction' :: Name -> Q Dec
mkFunction' name = do
    let newName = mkName $ nameBase name ++ "Schema"
        fn = EndpointName . pack $ nameBase name
    expression <- mkFunctionExp name fn
    pure $ FunD newName [Clause [] (NormalB expression) []]

{-# ANN mkFunctionExp ("HLint: ignore" :: String) #-}

mkFunctionExp :: Name -> EndpointName -> Q Exp
mkFunctionExp name fn = do
    r <- reify name
    case r of
        (VarI _ as _) ->
            let ts = args as
             in toSchemas fn ts
        _ -> error "Incorrect Name type provided to mkFunction"

{-# ANN toSchemas ("HLint: ignore Redundant bracket" :: String) #-}

toSchemas :: EndpointName -> [Type] -> Q Exp
toSchemas fn ts = do
    es <- foldr (\t e -> [|toSchema @($(pure t)) : $e|]) [|[]|] ts
    [|FunctionSchema fn $(pure es)|]

{-# ANN args ("HLint: ignore" :: String) #-}

args :: Type -> [Type]
args (AppT (AppT ArrowT t1) as) = t1 : args as
args (AppT (ConT _) _)          = []
args (AppT (AppT (ConT _) _) _) = []
args (ForallT _ _ as)           = args as
args (ConT _)                   = []
args (TupleT _)                 = []
args (AppT (VarT _) t)          = args t
args a                          = error $ "incorrect type in template haskell function: " ++ show a

mkKnownCurrencies :: [Name] -> Q [Dec]
mkKnownCurrencies ks = do
    let name = mkName registeredKnownCurrenciesBindingName
        sig = SigD name (AppT ListT (ConT (mkName "KnownCurrency")))
        names = fmap VarE ('Playground.Types.adaCurrency : ks)
        body = NormalB (ListE names)
        val = ValD (VarP name) body []
    pure [sig, val]
