{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
module TH.TestTH where

import           Language.Haskell.TH
import           Language.PlutusTx.Prelude

{-# ANN module "HLint: ignore" #-}

power :: Integer -> Q (TExp (Integer -> Integer))
power n =
    if n <= 0 then
        [|| \ _ -> (1::Integer) ||]
    else if even n then
        [|| \(x::Integer) -> let y = $$(power ($$divide n (2::Integer))) x in $$multiply y y ||]
    else
        [|| \(x::Integer) -> $$multiply x ($$(power ($$minus n (1::Integer))) x) ||]

andTH :: Q (TExp (Bool -> Bool -> Bool))
andTH = [||\(a :: Bool) -> \(b::Bool) -> if a then if b then True else False else False||]
