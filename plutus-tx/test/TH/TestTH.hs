{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
module TH.TestTH where

import           Language.Haskell.TH
import           Language.PlutusTx.Prelude

{-# ANN module "HLint: ignore" #-}

power :: Int -> Q (TExp (Int -> Int))
power n =
    if n <= 0 then
        [|| \ _ -> (1::Int) ||]
    else if even n then
        [|| \(x::Int) -> let y = $$(power ($$divide n (2::Int))) x in $$multiply y y ||]
    else
        [|| \(x::Int) -> $$multiply x ($$(power ($$minus n (1::Int))) x) ||]

andTH :: Q (TExp (Bool -> Bool -> Bool))
andTH = [||\(a :: Bool) -> \(b::Bool) -> if a then if b then True else False else False||]
