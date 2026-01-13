{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}

module BuiltinList.Budget.Spec where

import PlutusTx.Prelude hiding (mapMaybe)

import PlutusTx.BuiltinList qualified as L
import PlutusTx.Builtins qualified as B
import PlutusTx.Code (CompiledCode, unsafeApplyCode)
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.TH (compile)
import PlutusTx.Test (goldenBundle)
import System.FilePath ((</>))
import Test.Tasty.Extras (TestNested, testNested, testNestedGhc)

tests :: TestNested
tests =
  testNested ("BuiltinList" </> "Budget")
    . pure
    $ testNestedGhc
      [ goldenBundle "map" map (map `unsafeApplyCode` l1)
      , goldenBundle "elem" elem (elem `unsafeApplyCode` l1)
      , goldenBundle "find" find (find `unsafeApplyCode` l1)
      , goldenBundle "any" any (any `unsafeApplyCode` l1)
      , goldenBundle "all" all (all `unsafeApplyCode` l1)
      , goldenBundle "index" index (index `unsafeApplyCode` l1)
      , goldenBundle "indexNegative" indexNegative (indexNegative `unsafeApplyCode` l1)
      , goldenBundle "indexTooLarge" indexTooLarge (indexTooLarge `unsafeApplyCode` l1)
      , goldenBundle "cons" cons (cons `unsafeApplyCode` l1)
      , goldenBundle "unconsJust" unconsJust (unconsJust `unsafeApplyCode` l1)
      , goldenBundle "unconsNothing" unconsNothing (unconsNothing `unsafeApplyCode` l1)
      , goldenBundle "unsafeUnconsOk" unsafeUnconsOk (unsafeUnconsOk `unsafeApplyCode` l1)
      , goldenBundle "empty" empty (empty `unsafeApplyCode` l1)
      , goldenBundle "singleton" singleton (singleton `unsafeApplyCode` l1)
      , goldenBundle "null" null (null `unsafeApplyCode` l1)
      , goldenBundle "concat_operator" (++) ((++) `unsafeApplyCode` l1)
      , goldenBundle "cons_operator" (<|) ((<|) `unsafeApplyCode` l1)
      , goldenBundle "append" append (append `unsafeApplyCode` l1)
      , goldenBundle "findIndices" findIndices (findIndices `unsafeApplyCode` l1)
      , goldenBundle "filter" filter (filter `unsafeApplyCode` l1)
      , goldenBundle "mapMaybe" mapMaybe (mapMaybe `unsafeApplyCode` l1)
      , goldenBundle "length" length (length `unsafeApplyCode` l1)
      , goldenBundle "and" and (and `unsafeApplyCode` l2)
      , goldenBundle "or" or (or `unsafeApplyCode` l2)
      , goldenBundle "notElem" notElem (notElem `unsafeApplyCode` l1)
      , goldenBundle "foldr" foldr (foldr `unsafeApplyCode` l1)
      , goldenBundle "foldl" foldl (foldl `unsafeApplyCode` l1)
      , goldenBundle "listToMaybeJust" listToMaybeJust (listToMaybeJust `unsafeApplyCode` l1)
      , goldenBundle
          "listToMaybeNothing"
          listToMaybeNothing
          (listToMaybeNothing `unsafeApplyCode` l1)
      , goldenBundle "uniqueElementJust" uniqueElementJust (uniqueElementJust `unsafeApplyCode` l1)
      , goldenBundle
          "uniqueElementNothing"
          uniqueElementNothing
          (uniqueElementNothing `unsafeApplyCode` l1)
      , goldenBundle "revAppend" revAppend (revAppend `unsafeApplyCode` l1)
      , goldenBundle "reverse" reverse (reverse `unsafeApplyCode` l1)
      , goldenBundle "replicate" replicate (replicate `unsafeApplyCode` l1)
      , goldenBundle "findIndexJust" findIndexJust (findIndexJust `unsafeApplyCode` l1)
      , goldenBundle "findIndexNothing" findIndexNothing (findIndexNothing `unsafeApplyCode` l1)
      , goldenBundle "headOk" headOk (headOk `unsafeApplyCode` l1)
      , goldenBundle "headEmpty" headEmpty (headEmpty `unsafeApplyCode` l1)
      , goldenBundle "lastOk" lastOk (lastOk `unsafeApplyCode` l1)
      , goldenBundle "lastEmpty" lastEmpty (lastEmpty `unsafeApplyCode` l1)
      , goldenBundle "tailOk" tailOk (tailOk `unsafeApplyCode` l1)
      , goldenBundle "tailEmpty" tailEmpty (tailEmpty `unsafeApplyCode` l1)
      , goldenBundle "take" take (take `unsafeApplyCode` l1)
      , goldenBundle "drop" drop (drop `unsafeApplyCode` l1)
      , goldenBundle "dropWhile" dropWhile (dropWhile `unsafeApplyCode` l1)
      , goldenBundle "elemBy" elemBy (elemBy `unsafeApplyCode` l1)
      , goldenBundle "nub" nub (nub `unsafeApplyCode` l1)
      , goldenBundle "nubBy" nubBy (nubBy `unsafeApplyCode` l1)
      , goldenBundle "concat" concat (concat `unsafeApplyCode` l4)
      , goldenBundle "concatMap" concatMap (concatMap `unsafeApplyCode` l1)
      , goldenBundle "zipWith" zipWith (zipWith `unsafeApplyCode` l1)
      ]

map :: CompiledCode (L.BuiltinList Integer -> L.BuiltinList Integer)
map = $$(compile [||L.map (+ 1)||])

elem :: CompiledCode (L.BuiltinList Integer -> (Bool, Bool))
elem = $$(compile [||\xs -> (L.elem 8 xs, L.elem 12 xs)||])

find :: CompiledCode (L.BuiltinList Integer -> (Maybe Integer, Maybe Integer))
find = $$(compile [||\xs -> (L.find (>= 8) xs, L.find (>= 12) xs)||])

any :: CompiledCode (L.BuiltinList Integer -> (Bool, Bool))
any = $$(compile [||\xs -> (L.any (>= 8) xs, L.any (>= 12) xs)||])

all :: CompiledCode (L.BuiltinList Integer -> (Bool, Bool))
all = $$(compile [||\xs -> (L.all (>= 8) xs, L.all (>= 0) xs)||])

index :: CompiledCode (L.BuiltinList Integer -> Integer)
index = $$(compile [||\xs -> xs L.!! 5||])

indexNegative :: CompiledCode (L.BuiltinList Integer -> Integer)
indexNegative = $$(compile [||\xs -> xs L.!! (-1)||])

indexTooLarge :: CompiledCode (L.BuiltinList Integer -> Integer)
indexTooLarge = $$(compile [||\xs -> xs L.!! 10||])

cons :: CompiledCode (L.BuiltinList Integer -> L.BuiltinList Integer)
cons = $$(compile [||\xs -> L.cons 0 xs||])

unconsJust :: CompiledCode (L.BuiltinList Integer -> Maybe (Integer, L.BuiltinList Integer))
unconsJust = $$(compile [||\xs -> L.uncons xs||])

unconsNothing :: CompiledCode (L.BuiltinList Integer -> Maybe (Integer, L.BuiltinList Integer))
unconsNothing = $$(compile [||\_ -> L.uncons L.empty||])

unsafeUnconsOk :: CompiledCode (L.BuiltinList Integer -> (Integer, L.BuiltinList Integer))
unsafeUnconsOk = $$(compile [||\xs -> B.unsafeUncons xs||])

empty :: CompiledCode (L.BuiltinList Integer -> L.BuiltinList Integer)
empty = $$(compile [||\_ -> L.empty||])

singleton :: CompiledCode (L.BuiltinList Integer -> L.BuiltinList Integer)
singleton = $$(compile [||\_ -> L.singleton 42||])

null :: CompiledCode (L.BuiltinList Integer -> Bool)
null = $$(compile [||\xs -> L.null xs||])

(++) :: CompiledCode (L.BuiltinList Integer -> L.BuiltinList Integer)
(++) = $$(compile [||\xs -> xs L.++ xs||])

(<|) :: CompiledCode (L.BuiltinList Integer -> L.BuiltinList Integer)
(<|) = $$(compile [||\xs -> 42 L.<| xs||])

append :: CompiledCode (L.BuiltinList Integer -> L.BuiltinList Integer)
append = $$(compile [||\xs -> L.append xs xs||])

findIndices :: CompiledCode (L.BuiltinList Integer -> L.BuiltinList Integer)
findIndices = $$(compile [||\xs -> L.findIndices odd xs||])

filter :: CompiledCode (L.BuiltinList Integer -> L.BuiltinList Integer)
filter = $$(compile [||\xs -> L.filter even xs||])

mapMaybe :: CompiledCode (L.BuiltinList Integer -> L.BuiltinList Integer)
mapMaybe = $$(compile [||\xs -> L.mapMaybe (\x -> if odd x then Just x else Nothing) xs||])

length :: CompiledCode (L.BuiltinList Integer -> Integer)
length = $$(compile [||\xs -> L.length xs||])

and :: CompiledCode (L.BuiltinList Bool -> Bool)
and = $$(compile [||\xs -> L.and xs||])

or :: CompiledCode (L.BuiltinList Bool -> Bool)
or = $$(compile [||\xs -> L.or xs||])

notElem :: CompiledCode (L.BuiltinList Integer -> Bool)
notElem = $$(compile [||\xs -> L.notElem 42 xs||])

foldr :: CompiledCode (L.BuiltinList Integer -> Integer)
foldr = $$(compile [||\xs -> L.foldr (+) 0 xs||])

foldl :: CompiledCode (L.BuiltinList Integer -> Integer)
foldl = $$(compile [||\xs -> L.foldl (*) 1 xs||])

listToMaybeJust :: CompiledCode (L.BuiltinList Integer -> Maybe Integer)
listToMaybeJust = $$(compile [||\xs -> L.listToMaybe xs||])

listToMaybeNothing :: CompiledCode (L.BuiltinList Integer -> Maybe Integer)
listToMaybeNothing = $$(compile [||\_ -> L.listToMaybe L.empty||])

uniqueElementJust :: CompiledCode (L.BuiltinList Integer -> Maybe Integer)
uniqueElementJust = $$(compile [||\xs -> L.uniqueElement (L.take 1 xs)||])

uniqueElementNothing :: CompiledCode (L.BuiltinList Integer -> Maybe Integer)
uniqueElementNothing = $$(compile [||\_ -> L.uniqueElement L.empty||])

revAppend :: CompiledCode (L.BuiltinList Integer -> L.BuiltinList Integer)
revAppend = $$(compile [||\xs -> L.revAppend xs xs||])

reverse :: CompiledCode (L.BuiltinList Integer -> L.BuiltinList Integer)
reverse = $$(compile [||\xs -> L.reverse xs||])

replicate :: CompiledCode (L.BuiltinList Integer -> L.BuiltinList Integer)
replicate = $$(compile [||\_ -> L.replicate 10 0||])

findIndexJust :: CompiledCode (L.BuiltinList Integer -> Maybe Integer)
findIndexJust = $$(compile [||\xs -> L.findIndex (== 4) xs||])

findIndexNothing :: CompiledCode (L.BuiltinList Integer -> Maybe Integer)
findIndexNothing = $$(compile [||\xs -> L.findIndex (== 99) xs||])

zipWith :: CompiledCode (L.BuiltinList Integer -> L.BuiltinList Integer)
zipWith = $$(compile [||\xs -> L.zipWith (+) xs xs||])

headOk :: CompiledCode (L.BuiltinList Integer -> Integer)
headOk = $$(compile [||\xs -> L.head xs||])

headEmpty :: CompiledCode (L.BuiltinList Integer -> Integer)
headEmpty = $$(compile [||\_ -> L.head L.empty||])

lastOk :: CompiledCode (L.BuiltinList Integer -> Integer)
lastOk = $$(compile [||\xs -> L.last xs||])

lastEmpty :: CompiledCode (L.BuiltinList Integer -> Integer)
lastEmpty = $$(compile [||\_ -> L.last L.empty||])

tailOk :: CompiledCode (L.BuiltinList Integer -> L.BuiltinList Integer)
tailOk = $$(compile [||\xs -> L.tail xs||])

tailEmpty :: CompiledCode (L.BuiltinList Integer -> L.BuiltinList Integer)
tailEmpty = $$(compile [||\_ -> L.tail L.empty||])

take :: CompiledCode (L.BuiltinList Integer -> L.BuiltinList Integer)
take = $$(compile [||\xs -> L.take 5 xs||])

drop :: CompiledCode (L.BuiltinList Integer -> L.BuiltinList Integer)
drop = $$(compile [||\xs -> L.drop 5 xs||])

dropWhile :: CompiledCode (L.BuiltinList Integer -> L.BuiltinList Integer)
dropWhile = $$(compile [||\xs -> L.dropWhile (< 5) xs||])

elemBy :: CompiledCode (L.BuiltinList Integer -> Bool)
elemBy = $$(compile [||\xs -> L.elemBy (<=) 0 xs||])

nub :: CompiledCode (L.BuiltinList Integer -> L.BuiltinList Integer)
nub = $$(compile [||\xs -> L.nub (L.append xs xs)||])

nubBy :: CompiledCode (L.BuiltinList Integer -> L.BuiltinList Integer)
nubBy = $$(compile [||\xs -> L.nubBy (<=) xs||])

l1 :: CompiledCode (L.BuiltinList Integer)
l1 = liftCodeDef $ toBuiltin ([1 .. 10] :: [Integer])

l2 :: CompiledCode (L.BuiltinList Bool)
l2 = liftCodeDef $ toBuiltin ([True, False, True, False] :: [Bool])

l3 :: CompiledCode (L.BuiltinList (BuiltinPair Integer Integer))
l3 = liftCodeDef $ toBuiltin ([(1, 2), (3, 4), (5, 6)] :: [(Integer, Integer)])

l4 :: CompiledCode (L.BuiltinList (L.BuiltinList Integer))
l4 = liftCodeDef $ toBuiltin ([[1, 2], [3, 4]] :: [[Integer]])

concat :: CompiledCode (L.BuiltinList (L.BuiltinList Integer) -> L.BuiltinList Integer)
concat = $$(compile [||\xss -> L.concat xss||])

concatMap :: CompiledCode (L.BuiltinList Integer -> L.BuiltinList Integer)
concatMap = $$(compile [||\xss -> L.concatMap (L.replicate 2) xss||])
