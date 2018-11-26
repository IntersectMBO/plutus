{-# LANGUAGE TemplateHaskell #-}
module Language.PlutusTx.Prelude where

import qualified Language.PlutusTx.Builtins as Builtins

import Language.Haskell.TH

toPlutusString :: Q (TExp (String -> Builtins.String))
toPlutusString =
    [||
    let f str = case str of
            [] -> Builtins.emptyString
            (c:rest) -> Builtins.charToString c `Builtins.appendString` f rest
    in f
    ||]
