{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

module PlutusTx.Compiler.Precompiled where

import Debug.Trace
import PlutusCore.Pretty

import Data.ByteString qualified as BS
import Data.FileEmbed
import Flat
import Language.Haskell.TH.Lib qualified as TH
import Language.Haskell.TH.Syntax qualified as TH
import System.FilePath

import GHC.Types.Name qualified as GHC

import PlutusIR qualified as PIR
import PlutusIR.Compiler.Definitions qualified as PIR
import PlutusIR.MkPir qualified as PIR
import PlutusTx
import PlutusTx.Builtins qualified
import PlutusTx.Code qualified as PlutusTx
import PlutusTx.Compiler.Types
import PlutusTx.Compiler.Utils

precompiledTermsPath :: FilePath
precompiledTermsPath = "precompiled"

preCompiledTerms :: [TH.Name]
preCompiledTerms =
  [ 'PlutusTx.Builtins.equalsInteger
  ]

-- test :: ()
-- test =
--   let
--     foo =  [||PlutusTx.Builtins.equalsInteger||]
--   in ()

precompile :: TH.Name -> TH.Q TH.Exp
precompile name = do
  let
    fileName = precompiledTermsPath </> Prelude.show name
    foo :: TH.Code TH.Q (Integer -> Integer -> Bool)
    foo = (TH.Code $ pure $ TH.TExp $ TH.VarE name)
    compiled = TH.unType <$> (TH.examineCode $ PlutusTx.compile foo)

  [| case $(compiled) of
       PlutusTx.SerializedCode _ (Just pir) _ -> do
         BS.writeFile $(TH.lift fileName) pir
       _ -> putStrLn $ "Compilation result of " <> $(TH.lift $ show name) <> "does not have PIR"
      |]

precompileMain :: TH.Q TH.Exp
precompileMain = TH.doE $ TH.noBindS . precompile <$> preCompiledTerms

definePrecompiledTerm :: TH.Name -> TH.Q TH.Exp
definePrecompiledTerm name = do
  let
    filePath = precompiledTermsPath </> Prelude.show name
    pirRaw = embedFileIfExists filePath

  [| case ($pirRaw :: Maybe BS.ByteString) of
      Nothing -> pure ()
      Just pirRaw' ->
        case unflat @(PIR.Program _ _ _ _ SrcSpans) pirRaw' of
          Left _ -> pure ()
          Right pir -> do
            ghcId <- lookupGhcId name
            var <- compileVarFresh annMayInline ghcId
            PIR.defineTerm
              (LexName (GHC.getName ghcId))
              (PIR.Def
                 var
                 ((annMayInline <$ pir) ^. PIR.progTerm, PIR.Strict))
              mempty
   |]

definePrecompiledTerms :: TH.Q TH.Exp
definePrecompiledTerms = TH.doE $ TH.noBindS . definePrecompiledTerm <$> preCompiledTerms
