-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}

module TH.TestTH where

import Language.Haskell.TH
import PlutusTx.Builtins
import PlutusTx.Prelude

{- HLINT ignore -}

power :: Integer -> Code Q (Integer -> Integer)
power n =
  if n <= 0
    then
      [||\_ -> (1 :: Integer)||]
    else
      if even n
        then
          [||
          \(x :: Integer) -> let y = $$(power (n `divideInteger` (2 :: Integer))) x in y `multiplyInteger` y
          ||]
        else
          [||\(x :: Integer) -> x `multiplyInteger` ($$(power (n `subtractInteger` (1 :: Integer))) x)||]

andTH :: Code Q (Bool -> Bool -> Bool)
andTH = [||\(a :: Bool) -> \(b :: Bool) -> if a then if b then True else False else False||]
