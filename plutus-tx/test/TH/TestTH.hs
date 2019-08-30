{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NoImplicitPrelude   #-}
module TH.TestTH where

import           Language.Haskell.TH
import           Language.PlutusTx.Prelude
import           Language.PlutusTx.Builtins

{-# ANN module "HLint: ignore" #-}

power :: Integer -> Q (TExp (Integer -> Integer))
power n =
    if n <= 0 then
        [|| \ _ -> (1::Integer) ||]
    else if even n then
        [|| \(x::Integer) -> let y = $$(power (n `divideInteger` (2::Integer))) x in y `multiplyInteger` y ||]
    else
        [|| \(x::Integer) -> x `multiplyInteger` ($$(power (n `subtractInteger` (1::Integer))) x) ||]

andTH :: Q (TExp (Bool -> Bool -> Bool))
andTH = [||\(a :: Bool) -> \(b::Bool) -> if a then if b then True else False else False||]
