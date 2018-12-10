{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS -fplugin Language.PlutusTx.Plugin -fplugin-opt Language.PlutusTx.Plugin:dont-typecheck #-}
-- the simplfiier messes with things otherwise
{-# OPTIONS_GHC   -O0 #-}

-- | Terms which currently fail the typechecker, but which should work in future.
-- In a separate file so we can give different options to the plugin.
module Plugin.IllTyped where

import           Language.PlutusTx.Plugin

-- this module does lots of weird stuff deliberately
{-# ANN module "HLint: ignore" #-}

string :: CompiledCode
string = plc @"string" "test"

listConstruct :: CompiledCode
listConstruct = plc @"listConstruct" ([]::[Int])

listConstruct2 :: CompiledCode
listConstruct2 = plc @"listConstruct2" ([1]::[Int])

-- It is very difficult to get GHC to make a non-polymorphic redex if you use
-- list literal syntax with integers. But this works.
listConstruct3 :: CompiledCode
listConstruct3 = plc @"listConstruct3" ((1::Int):(2::Int):(3::Int):[])

listMatch :: CompiledCode
listMatch = plc @"listMatch" (\(l::[Int]) -> case l of { (x:_) -> x ; [] -> 0; })

data B a = One a | Two (B (a, a))

ptreeConstruct :: CompiledCode
ptreeConstruct = plc @"ptreeConstruct" (Two (Two (One ((1,2),(3,4)))) :: B Int)

-- TODO: replace this with 'first' when we have working recursive functions
ptreeMatch :: CompiledCode
ptreeMatch = plc @"ptreeMatch" (\(t::B Int) -> case t of { One a -> a; Two _ -> 2; })

sumDirect :: CompiledCode
sumDirect = plc @"sumDirect" (
    let sum :: [Int] -> Int
        sum []     = 0
        sum (x:xs) = x + sum xs
    in sum)

-- This doesn't work: we can't handle things that aren't of plain function type, and fold
-- is a universally quantified function type
{-
sumViaFold :: CompiledCode
sumViaFold = plc (let fold :: (a -> b -> a) -> a -> [b] -> a
                      fold f base l = case l of
                          [] -> base
                          (x:xs) -> f (fold f base xs) x
                      sum :: [Int] -> Int
                      sum = fold (+) 0
                  in sum)
-}

data Tree a = NodeTree a (Forest a)
data Forest a = NilForest | ConsForest (Tree a) (Forest a)
