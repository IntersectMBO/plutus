{-# LANGUAGE TemplateHaskell #-}
module Language.PlutusTx.Prelude (
    -- * String and tracing functions
    toPlutusString,
    trace,
    traceH,
    -- error is the only builtin that people are likely to want to use directly
    -- * Re-exported builtins
    error,
    -- * Boolean operators
    and,
    or,
    not,
    -- * Numbers
    min,
    max,
    -- * Maybe
    isJust,
    isNothing,
    maybe,
    -- * Lists
    map,
    foldr,
    length,
    all) where

import           Prelude                    (Bool (..), Int, Maybe (..), String, (<), (>), (+))

import qualified Language.PlutusTx.Builtins as Builtins
import           Language.PlutusTx.Builtins (error)

import           Language.Haskell.TH

-- | Convert a Haskell 'String' into a 'Builtins.String'.
toPlutusString :: Q (TExp (String -> Builtins.String))
toPlutusString =
    [||
    let f str = case str of
            [] -> Builtins.emptyString
            (c:rest) -> Builtins.charToString c `Builtins.appendString` f rest
    in f
    ||]

-- | Emit the given string as a trace message before evaluating the argument.
trace :: Q (TExp (Builtins.String -> a -> a))
trace = [||
         -- The builtin trace is just a side-effecting function that returns unit, so
         -- we have to be careful to make sure it actually gets evaluated, and not
         -- thrown away by GHC or the PIR compiler.
         \str a -> case (Builtins.trace str) of () -> a
         ||]

-- | A version of 'trace' that takes a Haskell 'String'.
traceH :: Q (TExp (String -> a -> a))
traceH = [|| \str a -> $$(trace) ($$(toPlutusString) str) a||]

-- | Logical AND
and :: Q (TExp (Bool -> Bool -> Bool))
and = [|| \(l :: Bool) (r :: Bool) -> if l then r else False ||]

-- | Logical OR
or :: Q (TExp (Bool -> Bool -> Bool))
or = [|| \(l :: Bool) (r :: Bool) -> if l then True else r ||]

-- | Logical negation
not :: Q (TExp (Bool -> Bool))
not = [|| \(a :: Bool) -> if a then False else True  ||]

-- | The smaller of two `Int`s
min :: Q (TExp (Int -> Int -> Int))
min = [|| \(a :: Int) (b :: Int) -> if a < b then a else b ||]

-- | The larger of two `Int`s
max :: Q (TExp (Int -> Int -> Int))
max = [|| \(a :: Int) (b :: Int) -> if a > b then a else b ||]

isJust :: Q (TExp (Maybe a -> Bool))
isJust = [|| \(m :: Maybe a) -> case m of { Just _ -> True; _ -> False; } ||]

isNothing :: Q (TExp (Maybe a -> Bool))
isNothing = [|| \(m :: Maybe a) -> case m of { Just _ -> False; } ||]

maybe :: Q (TExp (b -> (a -> b) -> Maybe a -> b))
maybe = [|| \b f m ->
    case m of
        Nothing -> b
        Just a  -> f a ||]

map :: Q (TExp ((a -> b) -> [a] -> [b]))
map = [||
    \f l ->
        let go ls = case ls of
                x:xs -> f x : go xs
                _    -> []
        in go l
        ||]

foldr :: Q (TExp ((a -> b -> b) -> b -> [a] -> b))
foldr = [||
    \f b l ->
        let go cur as = case as of
                []    -> cur
                a:as' -> go (f a cur) as'
        in go b l
    ||]

length :: Q (TExp ([a] -> Int))
length = [||
    \l ->
        -- it would be nice to define length in terms of foldr,
        -- but we can't, due to staging restrictions.
        let go lst = case lst of
                []   -> 0::Int
                _:xs -> 1 + go xs
        in go l
    ||]

all :: Q (TExp ((a -> Bool) -> [a] -> Bool))
all = [||
    \pred l ->
        let and' a b = if a then b else False
            go lst = case lst of
                []   -> True
                x:xs -> pred x `and'` go xs
        in go l
    ||]

