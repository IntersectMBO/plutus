{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
-- Need `+` for doctests, annoyingly
{-# OPTIONS_GHC -Wno-unused-imports #-}
-- | The prelude functions are split into dependent modules so that we obey the TH staging restriction when
-- reusing functions.
module Language.PlutusTx.Prelude.Stage0 where

import           Data.ByteString.Lazy       (ByteString)
import           Prelude                    (Bool (..), Int, Maybe (..), String, (<), (>), (+))

import qualified Language.PlutusTx.Builtins as Builtins

import           Language.Haskell.TH

-- | Terminate the evaluation of the script with an error message
error :: Q (TExp (() -> a))
error = [|| Builtins.error ||]

-- | Convert a Haskell 'String' into a PlutusTx 'Builtins.String'.
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
--
--   >>> $$([|| $$(and) True False ||])
--   False
--
and :: Q (TExp (Bool -> Bool -> Bool))
and = [|| \(l :: Bool) (r :: Bool) -> if l then r else False ||]

-- | Logical OR
--
--   >>> $$([|| $$(or) True False ||])
--   True
--
or :: Q (TExp (Bool -> Bool -> Bool))
or = [|| \(l :: Bool) (r :: Bool) -> if l then True else r ||]

-- | Logical negation
--
--   >>> $$([|| $$(not) True ||])
--   False
--
not :: Q (TExp (Bool -> Bool))
not = [|| \(a :: Bool) -> if a then False else True  ||]

-- | The smaller of two 'Int's
--
--   >>> $$([|| $$(min) 10 5 ||])
--   5
--
min :: Q (TExp (Int -> Int -> Int))
min = [|| \(a :: Int) (b :: Int) -> if a < b then a else b ||]

-- | The larger of two 'Int's
--
--   >>> $$([|| $$(max) 10 5 ||])
--   10
--
max :: Q (TExp (Int -> Int -> Int))
max = [|| \(a :: Int) (b :: Int) -> if a > b then a else b ||]

-- | Check if a 'Maybe' @a@ is @Just a@
--
--   >>> $$([|| $$(isJust) Nothing ||])
--   False
--   >>> $$([|| $$(isJust) (Just "plutus") ||])
--   True
--
isJust :: Q (TExp (Maybe a -> Bool))
isJust = [|| \m -> case m of { Just _ -> True; _ -> False; } ||]

-- | Check if a 'Maybe' @a@ is @Nothing@
--
--   >>> $$([|| $$(isNothing) Nothing ||])
--   True
--   >>> $$([|| $$(isNothing) (Just "plutus") ||])
--   False
--
isNothing :: Q (TExp (Maybe a -> Bool))
isNothing = [|| \m -> case m of { Just _ -> False; _ -> True; } ||]

-- | PlutusTx version of 'Prelude.maybe'.
--
--   >>> $$([|| $$(maybe) "platypus" (\s -> s) (Just "plutus") ||])
--   "plutus"
--   >>> $$([|| $$(maybe) "platypus" (\s -> s) Nothing ||])
--   "platypus"
--
maybe :: Q (TExp (b -> (a -> b) -> Maybe a -> b))
maybe = [|| \b f m ->
    case m of
        Nothing -> b
        Just a  -> f a ||]

-- | PlutusTx version of 'Data.List.map'.
--
--   >>> $$([|| $$(map) (\i -> i + 1) [1, 2, 3] ||])
--   [2,3,4]
--
map :: Q (TExp ((a -> b) -> [a] -> [b]))
map = [||
      let
          map :: (a -> b) -> [a] -> [b]
          map f l = case l of
              [] -> []
              x:xs -> f x : map f xs
      in map
        ||]

-- | PlutusTx version of 'Data.List.foldr'.
--
--   >>> $$([|| $$(foldr) (\i s -> s + i) 0 [1, 2, 3, 4] ||])
--   10
--
foldr :: Q (TExp ((a -> b -> b) -> b -> [a] -> b))
foldr = [||
        let
            foldr :: (a -> b -> b) -> b -> [a] -> b
            foldr f acc l = case l of
                [] -> acc
                x:xs -> f x (foldr f acc xs)
        in foldr
    ||]

-- | PlutusTx version of 'Data.List.foldl'.
--
--   >>> $$([|| $$(foldl) (\s i -> s + i) 0 [1, 2, 3, 4] ||])
--   10
--
foldl :: Q (TExp ((b -> a -> b) -> b -> [a] -> b))
foldl = [||
        let
            foldl :: (b -> a -> b) -> b -> [a] -> b
            foldl f acc l = case l of
                [] -> acc
                x:xs -> foldl f (f acc x) xs
        in foldl
    ||]

txhash :: Q (TExp ByteString)
txhash = [|| Builtins.txhash ||]

-- | The double SHA256 hash of a 'ByteString'
sha2_256 :: Q (TExp (ByteString -> ByteString))
sha2_256 = [|| Builtins.sha2_256 ||]

-- | The triple SHA256 hash of a 'ByteString'
sha3_256 :: Q (TExp (ByteString -> ByteString))
sha3_256 = [|| Builtins.sha3_256 ||]

-- | Check if two 'ByteString's are equal
equalsByteString :: Q (TExp (ByteString -> ByteString -> Bool))
equalsByteString = [|| Builtins.equalsByteString ||]

-- | Returns the n length prefix of a 'ByteString'
takeByteString :: Q (TExp (Int -> ByteString -> ByteString))
takeByteString = [|| Builtins.takeByteString ||]

-- | Returns the suffix of a 'ByteString' after n elements
dropByteString :: Q (TExp (Int -> ByteString -> ByteString))
dropByteString = [|| Builtins.dropByteString ||]

-- | Concatenates two 'ByteString's together.
concatenate :: Q (TExp (ByteString -> ByteString -> ByteString))
concatenate = [|| Builtins.concatenate ||]
