{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

module Playground.TH where

import           Data.Proxy
import           Data.Swagger.Schema (ToSchema, toInlinedSchema)
import           Language.Haskell.TH
import           Playground.API      (Fn (Fn), FunctionSchema (FunctionSchema))
import Data.Text (pack)

mkFunction :: Name -> Q [Dec]
mkFunction name = do
  let newName = mkName $ nameBase name ++ "Schema"
      fn = Fn . pack $ nameBase name
  exp <- mkFunction' name fn
  pure [FunD newName [Clause [] (NormalB exp) []]]

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
    foldr (\t e -> [|$e ++ [toInlinedSchema (Proxy :: Proxy $(pure t))]|]) [|[]|] ts
  [|FunctionSchema fn $(pure es)|]

args (AppT (AppT ArrowT t1) as) = t1 : args as
args (ForallT _ _ as)                          = args as
args (ConT _) = []
args (AppT (VarT v) t) = []
args a = error $ "incorrect type " ++ show a

-- ForallT
--   [KindedTV m_6989586621679068618 (AppT (AppT ArrowT StarT) StarT)]
--   [AppT (AppT (ConT Control.Monad.Error.Class.MonadError) (ConT Wallet.API.WalletAPIError)) (VarT m_6989586621679068618),AppT (ConT Wallet.API.WalletAPI) (VarT m_6989586621679068618)]
--   (AppT
--    (AppT ArrowT (ConT Main.Vesting))
--    (AppT
--     (AppT ArrowT (ConT Wallet.UTXO.Runtime.Value))
--     (AppT (VarT m_6989586621679068618) (TupleT 0))))


-- VarI Playground.Interpreter.isWalletFunction
--   (ForallT
--    [KindedTV m_6989586621679513522 (AppT (AppT ArrowT StarT) StarT)]
--    [AppT (ConT Hint.Base.MonadInterpreter) (VarT m_6989586621679513522)]
--    (AppT (AppT ArrowT (ConT Hint.Reflection.ModuleElem)) (AppT (VarT m_6989586621679513522) (AppT (ConT GHC.Base.Maybe) (ConT Hint.Reflection.ModuleElem))))) Nothing
