-- Need some extra imports from the Prelude for doctests, annoyingly
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Language.PlutusTx.Prelude (
    -- $prelude
    -- * Classes
    Eq (..),
    Ord (..),
    Functor (..),
    (<$>),
    (<$),
    -- * Functions
    const,
    -- * String and tracing functions
    toPlutusString,
    trace,
    traceH,
    traceIfTrueH,
    traceIfFalseH,
    traceErrorH,
    -- * Error
    error,
    check,
    -- * Boolean operators
    (&&),
    (||),
    not,
    -- * Int operators
    plus,
    minus,
    multiply,
    divide,
    remainder,
    -- * Tuples
    fst,
    snd,
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
    (++),
    filter,
    -- * ByteStrings
    ByteString,
    takeByteString,
    dropByteString,
    concatenate,
    emptyByteString,
    -- * Hashes and Signatures
    sha2_256,
    sha3_256,
    verifySignature,
    module Prelude
    ) where

import           Language.PlutusTx.Builtins (ByteString, concatenate, dropByteString, emptyByteString, equalsByteString,
                                             greaterThanByteString, lessThanByteString, sha2_256, sha3_256,
                                             takeByteString, verifySignature)
import qualified Language.PlutusTx.Builtins as Builtins
import           Prelude                    as Prelude hiding (Eq (..), Functor (..), Ord (..), all, any, const, error,
                                                        filter, foldl, foldr, fst, length, map, max, maybe, min, not,
                                                        null, snd, (&&), (++), (<$>), (||))

-- this module does lots of weird stuff deliberately
{-# ANN module ("HLint: ignore"::String) #-}

-- $prelude
-- The PlutusTx Prelude is a replacement for the Haskell Prelude that works
-- better with Plutus Tx. You should use it if you're writing code that
-- will be compiled with the Plutus Tx compiler.
-- @
--     {-# LANGUAGE NoImplicitPrelude #-}
--     import Language.PlutusTx.Prelude
-- @

-- $setup
-- >>> :set -XNoImplicitPrelude
-- >>> import Language.PlutusTx.Prelude

-- Copied from the GHC definition
-- | The 'Eq' class defines equality ('==') and inequality ('/=').
--
-- Minimal complete definition: either '==' or '/='.
--
class Eq a where
    (==), (/=)           :: a -> a -> Bool

    {-# INLINABLE (/=) #-}
    x /= y               = not (x == y)
    {-# INLINABLE (==) #-}
    x == y               = not (x /= y)

instance Eq Integer where
    {-# INLINABLE (==) #-}
    (==) = Builtins.equalsInteger

instance Eq ByteString where
    {-# INLINABLE (==) #-}
    (==) = Builtins.equalsByteString

instance Eq a => Eq [a] where
    {-# INLINABLE (==) #-}
    [] == [] = True
    (x:xs) == (y:ys) = x == y && xs == ys
    _ == _ = False

instance Eq Bool where
    {-# INLINABLE (==) #-}
    True == True = True
    False == False = True
    _ == _ = False

instance Eq a => Eq (Maybe a) where
    {-# INLINABLE (==) #-}
    (Just a1) == (Just a2) = a1 == a2
    Nothing == Nothing = True
    _ == _ = False

instance (Eq a, Eq b) => Eq (Either a b) where
    {-# INLINABLE (==) #-}
    (Left a1) == (Left a2) = a1 == a2
    (Right b1) == (Right b2) = b1 == b2
    _ == _ = False

instance Eq () where
    {-# INLINABLE (==) #-}
    _ == _ = True

instance (Eq a, Eq b) => Eq (a, b) where
    {-# INLINABLE (==) #-}
    (a, b) == (a', b') = a == a' && b == b'

-- Copied from the GHC definition
-- | The 'Ord' class is used for totally ordered datatypes.
--
-- Minimal complete definition: either 'compare' or '<='.
-- Using 'compare' can be more efficient for complex types.
--
class Eq a => Ord a where
    compare              :: a -> a -> Ordering
    (<), (<=), (>), (>=) :: a -> a -> Bool
    max, min             :: a -> a -> a

    {-# INLINABLE compare #-}
    compare x y = if x == y then EQ
                  -- NB: must be '<=' not '<' to validate the
                  -- above claim about the minimal things that
                  -- can be defined for an instance of Ord:
                  else if x <= y then LT
                  else GT

    {-# INLINABLE (<) #-}
    x <  y = case compare x y of { LT -> True;  _ -> False }
    {-# INLINABLE (<=) #-}
    x <= y = case compare x y of { GT -> False; _ -> True }
    {-# INLINABLE (>) #-}
    x >  y = case compare x y of { GT -> True;  _ -> False }
    {-# INLINABLE (>=) #-}
    x >= y = case compare x y of { LT -> False; _ -> True }

    -- These two default methods use '<=' rather than 'compare'
    -- because the latter is often more expensive
    {-# INLINABLE max #-}
    max x y = if x <= y then y else x
    {-# INLINABLE min #-}
    min x y = if x <= y then x else y

instance Ord Integer where
    {-# INLINABLE (<) #-}
    (<) = Builtins.lessThanInteger
    {-# INLINABLE (<=) #-}
    (<=) = Builtins.lessThanEqInteger
    {-# INLINABLE (>) #-}
    (>) = Builtins.greaterThanInteger
    {-# INLINABLE (>=) #-}
    (>=) = Builtins.greaterThanEqInteger

instance Ord ByteString where
    {-# INLINABLE compare #-}
    compare l r = if Builtins.lessThanByteString l r then LT else if Builtins.equalsByteString l r then EQ else GT

instance Ord a => Ord [a] where
    {-# INLINABLE compare #-}
    compare []     []     = EQ
    compare []     (_:_)  = LT
    compare (_:_)  []     = GT
    compare (x:xs) (y:ys) = case compare x y of
                                EQ    -> compare xs ys
                                other -> other

instance Ord Bool where
    {-# INLINABLE compare #-}
    compare b1 b2 = case b1 of
        False -> case b2 of
            False -> EQ
            True  -> LT
        True -> case b2 of
            False -> GT
            True  -> EQ

instance Ord a => Ord (Maybe a) where
    {-# INLINABLE compare #-}
    compare (Just a1) (Just a2) = compare a1 a2
    compare Nothing (Just _)    = LT
    compare (Just _) Nothing    = GT
    compare Nothing Nothing     = EQ

instance (Ord a, Ord b) => Ord (Either a b) where
    {-# INLINABLE compare #-}
    compare (Left a1) (Left a2)   = compare a1 a2
    compare (Left _) (Right _)    = LT
    compare (Right _) (Left _)    = GT
    compare (Right b1) (Right b2) = compare b1 b2

instance Ord () where
    {-# INLINABLE compare #-}
    compare _ _ = EQ

instance (Ord a, Ord b) => Ord (a, b) where
    {-# INLINABLE compare #-}
    compare (a, b) (a', b') = case compare a a' of
        LT -> LT
        GT -> GT
        EQ -> compare b b'

{- | The 'Functor' class is used for types that can be mapped over.
Instances of 'Functor' should satisfy the following laws:

> fmap id  ==  id
> fmap (f . g)  ==  fmap f . fmap g
-}
class Functor f where
    fmap :: (a -> b) -> f a -> f b

    -- <$ deliberately omitted, to make this a one-method class which has a
    -- simpler representation

infixl 4 <$>
-- | An infix synonym for 'fmap'.
{-# INLINABLE (<$>) #-}
(<$>) :: Functor f => (a -> b) -> f a -> f b
(<$>) f fa = fmap f fa

infixl 4 <$
{-# INLINABLE (<$) #-}
-- | Replace all locations in the input with the same value.
(<$) :: Functor f => a -> f b -> f a
(<$) a fb = fmap (const a) fb

instance Functor [] where
    {-# INLINABLE fmap #-}
    fmap f l = case l of
            []   -> []
            x:xs -> f x : fmap f xs

instance Functor Maybe where
    {-# INLINABLE fmap #-}
    fmap f (Just a) = Just (f a)
    fmap _ Nothing  = Nothing

instance Functor (Either c) where
    {-# INLINABLE fmap #-}
    fmap f (Right a) = Right (f a)
    fmap _ (Left c)  = Left c

instance Functor ((,) c) where
    {-# INLINABLE fmap #-}
    fmap f (c, a) = (c, f a)

{-# INLINABLE const #-}
-- | Plutus Tx version of 'Prelude.const'.
const                   :: a -> b -> a
const x _               =  x

{-# INLINABLE error #-}
-- | Terminate the evaluation of the script with an error message.
error :: () -> a
error = Builtins.error

{-# INLINABLE check #-}
-- | Checks a 'Bool' and aborts if it is false.
check :: Bool -> ()
check b = if b then () else error ()

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

{-# INLINABLE traceErrorH #-}
-- | Log a message and then terminate the evaluation with an error.
traceErrorH :: String -> a
traceErrorH str = error (traceH str ())

{-# INLINABLE traceIfFalseH #-}
-- | Emit the given Haskell 'String' only if the argument evaluates to 'False'.
traceIfFalseH :: String -> Bool -> Bool
traceIfFalseH str a = if a then True else traceH str False

{-# INLINABLE traceIfTrueH #-}
-- | Emit the given Haskell 'String' only if the argument evaluates to 'True'.
traceIfTrueH :: String -> Bool -> Bool
traceIfTrueH str a = if a then traceH str True else False

{-# INLINABLE (&&) #-}
-- | Logical AND
--
--   >>> True && False
--   False
--
infixr 3 &&
(&&) :: Bool -> Bool -> Bool
(&&) l r = if l then r else False

{-# INLINABLE (||) #-}
-- | Logical OR
--
--   >>> True || False
--   True
--
infixr 2 ||
(||) :: Bool -> Bool -> Bool
(||) l r = if l then True else r

{-# INLINABLE not #-}
-- | Logical negation
--
--   >>> not True
--   False
--
not :: Bool -> Bool
not a = if a then False else True

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
all p = foldr (\a acc -> acc && p a) True

{-# INLINABLE any #-}
-- | PlutusTx version of 'Data.List.any'.
--
--   >>> any (\i -> i > 5) [6, 2, 1]
--   True
--
any :: (a -> Bool) -> [a] -> Bool
any p = foldr (\a acc -> acc || p a) False

{-# INLINABLE (++) #-}
-- | PlutusTx version of 'Data.List.(++)'.
--
--   >>> [0, 1, 2] ++ [1, 2, 3, 4]
--   [0,1,2,1,2,3,4]
--
(++) :: [a] -> [a] -> [a]
(++) l r = foldr (:) r l

{-# INLINABLE filter #-}
-- | PlutusTx version of 'Data.List.filter'.
--
--   >>> filter (> 1) [1, 2, 3, 4]
--   [2,3,4]
--
filter :: (a -> Bool) -> [a] -> [a]
filter p = foldr (\e xs -> if p e then e:xs else xs) []

{-# INLINABLE mapMaybe #-}
-- | PlutusTx version of 'Data.Maybe.mapMaybe'.
--
--   >>> mapMaybe (\i -> if i == 2 then Just '2' else Nothing) [1, 2, 3, 4]
--   "2"
--
mapMaybe :: (a -> Maybe b) -> [a] -> [b]
mapMaybe p = foldr (\e xs -> case p e of { Just e' -> e':xs; Nothing -> xs}) []

{-# INLINABLE fst #-}
-- | PlutusTx version of 'Data.Tuple.fst'
fst :: (a, b) -> a
fst (a, _) = a

{-# INLINABLE snd #-}
-- | PlutusTx version of 'Data.Tuple.snd'
snd :: (a, b) -> b
snd (_, b) = b
