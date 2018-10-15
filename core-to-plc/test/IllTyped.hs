{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS -fplugin Language.Plutus.CoreToPLC.Plugin -fplugin-opt Language.Plutus.CoreToPLC.Plugin:dont-typecheck #-}
-- the simplfiier messes with things otherwise
{-# OPTIONS_GHC   -O0 #-}

-- | Terms which currently fail the typechecker, but which should work in future.
-- In a separate file so we can give different options to the plugin.
module IllTyped where

import           Language.Plutus.CoreToPLC.Plugin
import           Language.Plutus.CoreToPLC.Primitives as Prims

-- this module does lots of weird stuff deliberately
{-# ANN module "HLint: ignore" #-}

listConstruct :: PlcCode
listConstruct = plc ([]::[Int])

listConstruct2 :: PlcCode
listConstruct2 = plc ([1]::[Int])

-- It is very difficult to get GHC to make a non-polymorphic redex if you use
-- list literal syntax with integers. But this works.
listConstruct3 :: PlcCode
listConstruct3 = plc ((1::Int):(2::Int):(3::Int):[])

listMatch :: PlcCode
listMatch = plc (\(l::[Int]) -> case l of { (x:_) -> x ; [] -> 0; })

data B a = One a | Two (B (a, a))

ptreeConstruct :: PlcCode
ptreeConstruct = plc (Two (Two (One ((1,2),(3,4)))) :: B Int)

-- TODO: replace this with 'first' when we have working recursive functions
ptreeMatch :: PlcCode
ptreeMatch = plc (\(t::B Int) -> case t of { One a -> a; Two _ -> 2; })

sumDirect :: PlcCode
sumDirect = plc (
    let sum :: [Int] -> Int
        sum []     = 0
        sum (x:xs) = x + sum xs
    in sum)

-- This doesn't work: we can't handle things that aren't of plain function type, and fold
-- is a universally quantified function type
{-
sumViaFold :: PlcCode
sumViaFold = plc (let fold :: (a -> b -> a) -> a -> [b] -> a
                      fold f base l = case l of
                          [] -> base
                          (x:xs) -> f (fold f base xs) x
                      sum :: [Int] -> Int
                      sum = fold (+) 0
                  in sum)
-}

evenMutual :: PlcCode
evenMutual = plc (
    let even :: Int -> Bool
        even n = if n == 0 then True else odd (n-1)
        odd :: Int -> Bool
        odd n = if n == 0 then False else even (n-1)
    in even)
