{-# LANGUAGE NoImplicitPrelude #-}
-- Need some extra imports from the Prelude for doctests, annoyingly
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Language.PlutusTx.Prelude (
    -- $prelude
    -- * String and tracing functions
    toPlutusString,
    trace,
    traceH,
    traceIfTrueH,
    traceIfFalseH,
    -- * Error
    error,
    -- * Boolean operators
    and,
    or,
    not,
    -- * Int operators
    gt,
    geq,
    lt,
    leq,
    eq,
    plus,
    minus,
    multiply,
    divide,
    remainder,
    -- * Numbers
    min,
    max,
    -- * Maybe
    isJust,
    isNothing,
    maybe,
    mapMaybe,
    -- * Lists
    null,
    map,
    foldr,
    foldl,
    length,
    all,
    any,
    append,
    filter,
    -- * ByteStrings
    ByteString,
    equalsByteString,
    takeByteString,
    dropByteString,
    concatenate,
    emptyByteString,
    -- * Hashes and Signatures
    sha2_256,
    sha3_256,
    verifySignature
    ) where

import           Language.PlutusTx.Builtins (ByteString)
import qualified Language.PlutusTx.Builtins as Builtins
import           Prelude                    (Bool (..), Integer, Maybe (..), String, (+), (==), (>))

-- this module does lots of weird stuff deliberately
{-# ANN module ("HLint: ignore"::String) #-}

-- $prelude
-- The PlutusTx Prelude is a collection of useful functions that work with
-- builtin Haskell data types such as 'Maybe' and @[]@ (list).

{-# INLINABLE error #-}
-- | Terminate the evaluation of the script with an error message
error :: () -> a
error = Builtins.error

{-# INLINABLE toPlutusString #-}
-- | Convert a Haskell 'String' into a PlutusTx 'Builtins.String'.
toPlutusString :: String -> Builtins.String
toPlutusString str = case str of
    []       -> Builtins.emptyString
    (c:rest) -> Builtins.charToString c `Builtins.appendString` toPlutusString rest

{-# INLINABLE trace #-}
-- | Emit the given string as a trace message before evaluating the argument.
trace :: Builtins.String -> a -> a
-- The builtin trace is just a side-effecting function that returns unit, so
-- we have to be careful to make sure it actually gets evaluated, and not
-- thrown away by GHC or the PIR compiler.
trace str a = case Builtins.trace str of () -> a

{-# INLINABLE traceH #-}
-- | A version of 'trace' that takes a Haskell 'String'.
traceH :: String -> a -> a
traceH str = trace (toPlutusString str)

{-# INLINABLE traceIfFalseH #-}
-- | Emit the given Haskell 'String' only if the argument evaluates to 'False'.
traceIfFalseH :: String -> Bool -> Bool
traceIfFalseH str a = if a then True else traceH str False

{-# INLINABLE traceIfTrueH #-}
-- | Emit the given Haskell 'String' only if the argument evaluates to 'True'.
traceIfTrueH :: String -> Bool -> Bool
traceIfTrueH str a = if a then traceH str True else False

{-# INLINABLE and #-}
-- | Logical AND
--
--   >>> and True False
--   False
--
and :: Bool -> Bool -> Bool
and l r = if l then r else False

{-# INLINABLE or #-}
-- | Logical OR
--
--   >>> or True False
--   True
--
or :: Bool -> Bool -> Bool
or l r = if l then True else r

{-# INLINABLE not #-}
-- | Logical negation
--
--   >>> not True
--   False
--
not :: Bool -> Bool
not a = if a then False else True

{-# INLINABLE gt #-}
-- | Greater than
--
--   >>> gt 2 1
--   True
--
gt :: Integer -> Integer -> Bool
gt = Builtins.greaterThanInteger

{-# INLINABLE geq #-}
-- | Greater than or equal to
--
--   >>> geq 2 2
--   True
--
geq :: Integer -> Integer -> Bool
geq = Builtins.greaterThanEqInteger

{-# INLINABLE lt #-}
-- | Less than
--
--   >>> lt 2 1
--   False
--
lt :: Integer -> Integer -> Bool
lt = Builtins.lessThanInteger

{-# INLINABLE leq #-}
-- | Less than or equal to
--
--   >>> leq 2 2
--   True
--
leq :: Integer -> Integer -> Bool
leq = Builtins.lessThanEqInteger

{-# INLINABLE eq #-}
-- | Eq for 'Integer'
--
--   >>> eq 2 1
--   False
--
eq :: Integer -> Integer -> Bool
eq = Builtins.equalsInteger

{-# INLINABLE plus #-}
-- | Addition
--
--   >>> plus 2 1
--   3
--
plus :: Integer -> Integer -> Integer
plus = Builtins.addInteger

{-# INLINABLE minus #-}
-- | Subtraction
--
--   >>> minus 2 1
--   1
--
minus :: Integer -> Integer -> Integer
minus = Builtins.subtractInteger

{-# INLINABLE multiply #-}
-- | Multiplication
--
--   >>> multiply 2 1
--   2
--
multiply :: Integer -> Integer -> Integer
multiply = Builtins.multiplyInteger

{-# INLINABLE divide #-}
-- | Integer division
--
--   >>> divide 3 2
--   1
--
divide :: Integer -> Integer -> Integer
divide = Builtins.divideInteger

{-# INLINABLE remainder #-}
-- | Remainder (of integer division)
--
--   >>> remainder 3 2
--   1
--
remainder :: Integer -> Integer -> Integer
remainder = Builtins.remainderInteger

{-# INLINABLE min #-}
-- | The smaller of two 'Integer's
--
--   >>> min 10 5
--   5
--
min :: Integer -> Integer -> Integer
min a b = if Builtins.lessThanInteger a b then a else b

{-# INLINABLE max #-}
-- | The larger of two 'Integer's
--
--   >>> max 10 5
--   10
--
max :: Integer -> Integer -> Integer
max a b = if Builtins.greaterThanInteger a b then a else b

{-# INLINABLE isJust #-}
-- | Check if a 'Maybe' @a@ is @Just a@
--
--   >>> isJust Nothing
--   False
--   >>> isJust (Just "plutus")
--   True
--
isJust :: Maybe a -> Bool
isJust m = case m of { Just _ -> True; _ -> False; }

{-# INLINABLE isNothing #-}
-- | Check if a 'Maybe' @a@ is @Nothing@
--
--   >>> isNothing Nothing
--   True
--   >>> isNothing (Just "plutus")
--   False
--
isNothing :: Maybe a -> Bool
isNothing m = case m of { Just _ -> False; _ -> True; }

{-# INLINABLE maybe #-}
-- | PlutusTx version of 'Prelude.maybe'.
--
--   >>> maybe "platypus" (\s -> s) (Just "plutus")
--   "plutus"
--   >>> maybe "platypus" (\s -> s) Nothing
--   "platypus"
--
maybe :: b -> (a -> b) -> Maybe a -> b
maybe b f m = case m of
    Nothing -> b
    Just a  -> f a

{-# INLINABLE null #-}
-- | PlutusTx version of 'Data.List.null'.
--
--   >>> null [1]
--   False
--   >>> null []
--   True
--
null :: [a] -> Bool
null l = case l of
    [] -> True
    _  -> False

{-# INLINABLE map #-}
-- | PlutusTx version of 'Data.List.map'.
--
--   >>> map (\i -> i + 1) [1, 2, 3]
--   [2,3,4]
--
map :: (a -> b) -> [a] -> [b]
map f l = case l of
    []   -> []
    x:xs -> f x : map f xs

{-# INLINABLE foldr #-}
-- | PlutusTx version of 'Data.List.foldr'.
--
--   >>> foldr (\i s -> s + i) 0 [1, 2, 3, 4]
--   10
--
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f acc l = case l of
    []   -> acc
    x:xs -> f x (foldr f acc xs)

{-# INLINABLE foldl #-}
-- | PlutusTx version of 'Data.List.foldl'.
--
--   >>> foldl (\s i -> s + i) 0 [1, 2, 3, 4]
--   10
--
foldl :: (b -> a -> b) -> b -> [a] -> b
foldl f acc l = case l of
    []   -> acc
    x:xs -> foldl f (f acc x) xs

{-# INLINABLE sha2_256 #-}
-- | The double SHA256 hash of a 'ByteString'
sha2_256 :: Builtins.ByteString -> Builtins.ByteString
sha2_256 = Builtins.sha2_256

{-# INLINABLE sha3_256 #-}
-- | The triple SHA256 hash of a 'ByteString'
sha3_256 :: Builtins.ByteString -> Builtins.ByteString
sha3_256 = Builtins.sha3_256

{-# INLINABLE verifySignature #-}
verifySignature :: Builtins.ByteString -> Builtins.ByteString -> Builtins.ByteString -> Bool
verifySignature = Builtins.verifySignature

{-# INLINABLE equalsByteString #-}
-- | Check if two 'ByteString's are equal
equalsByteString :: Builtins.ByteString -> Builtins.ByteString -> Bool
equalsByteString = Builtins.equalsByteString

{-# INLINABLE takeByteString #-}
-- | Returns the n length prefix of a 'ByteString'
takeByteString :: Integer -> Builtins.ByteString -> Builtins.ByteString
takeByteString = Builtins.takeByteString

{-# INLINABLE dropByteString #-}
-- | Returns the suffix of a 'ByteString' after n elements
dropByteString :: Integer -> Builtins.ByteString -> Builtins.ByteString
dropByteString = Builtins.dropByteString

{-# INLINABLE concatenate #-}
-- | Concatenates two 'ByteString's together.
concatenate :: Builtins.ByteString -> Builtins.ByteString -> Builtins.ByteString
concatenate = Builtins.concatenate

{-# INLINABLE emptyByteString #-}
-- | An empty 'ByteString'.
emptyByteString :: Builtins.ByteString
emptyByteString = Builtins.emptyByteString

{-# INLINABLE length #-}
-- | 'length' @xs@ is the number of elements in @xs@.
--
--   >>> length [1, 2, 3, 4]
--   4
--
length :: [a] -> Integer
-- eta-expanded to avoid the value restriction
length as = foldr (\_ acc -> plus acc 1) 0 as

{-# INLINABLE all #-}
-- | PlutusTx version of 'Data.List.all'.
--
--   >>> all (\i -> i > 5) [6, 8, 12]
--   True
--
all :: (a -> Bool) -> [a] -> Bool
all pred = foldr (\a acc -> acc `and` pred a) True

{-# INLINABLE any #-}
-- | PlutusTx version of 'Data.List.any'.
--
--   >>> any (\i -> i > 5) [6, 2, 1]
--   True
--
any :: (a -> Bool) -> [a] -> Bool
any pred = foldr (\a acc -> acc `or` pred a) False

{-# INLINABLE append #-}
-- | PlutusTx version of 'Data.List.(++)'.
--
--   >>> append [0, 1, 2] [1, 2, 3, 4]
--   [0,1,2,1,2,3,4]
--
append :: [a] -> [a] -> [a]
append l r = foldr (:) r l

{-# INLINABLE filter #-}
-- | PlutusTx version of 'Data.List.filter'.
--
--   >>> filter (> 1) [1, 2, 3, 4]
--   [2,3,4]
--
filter :: (a -> Bool) -> [a] -> [a]
filter pred = foldr (\e xs -> if pred e then e:xs else xs) []

{-# INLINABLE mapMaybe #-}
-- | PlutusTx version of 'Data.Maybe.mapMaybe'.
--
--   >>> mapMaybe (\i -> if i == 2 then Just '2' else Nothing) [1, 2, 3, 4]
--   "2"
--
mapMaybe :: (a -> Maybe b) -> [a] -> [b]
mapMaybe pred = foldr (\e xs -> case pred e of { Just e' -> e':xs; Nothing -> xs}) []
