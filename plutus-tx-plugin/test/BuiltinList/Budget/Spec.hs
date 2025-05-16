{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}

module BuiltinList.Budget.Spec where

import Prelude hiding (all, any, elem, map)
import System.FilePath
import Test.Tasty (TestName)
import Test.Tasty.Extras

import PlutusTx.BuiltinList qualified as L
import PlutusTx.Builtins.HasBuiltin (HasToBuiltin (toBuiltin))
import PlutusTx.Code
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.Prelude qualified as P
import PlutusTx.Test
import PlutusTx.TH (compile)

tests :: TestNested
tests =
  testNested ("BuiltinList" </> "Budget") . pure $
    testNestedGhc
      [ goldenBundle "map" map (map `unsafeApplyCode` l)
      , goldenBundle "elem" elem (elem `unsafeApplyCode` l)
      , goldenBundle "find" find (find `unsafeApplyCode` l)
      , goldenBundle "any" any (any `unsafeApplyCode` l)
      , goldenBundle "all" all (all `unsafeApplyCode` l)
      , goldenBundle "index" index (index `unsafeApplyCode` l)
      , goldenBundle "indexNegative" (index `unsafeApplyCode` indexNegative l)
      , goldenBundle "indexTooLarge" (index `unsafeApplyCode` indexTooLarge l)
      , goldenBundle "cons" (index `unsafeApplyCode` cons l)
      , goldenBundle "unconsJust" (index `unsafeApplyCode` unconsJust l)
      , goldenBundle "unconsNothing" (index `unsafeApplyCode` unconsNothing l)
      ]


-- goldenBundle :: TestName -> _ -> _ -> TestNested
goldenBundle name f x = do
  goldenPirReadable name f
  goldenUPlcReadable name f
  goldenEvalCekCatch name [f `unsafeApplyCode` x]
  goldenBudget name (f `unsafeApplyCode` x)


map :: CompiledCode (P.BuiltinList Integer -> P.BuiltinList Integer)
map = $$(compile [||L.map (P.+ 1)||])

elem :: CompiledCode (P.BuiltinList Integer -> (Bool, Bool))
elem = $$(compile [||\xs -> (L.elem 8 xs, L.elem 12 xs)||])

find :: CompiledCode (P.BuiltinList Integer -> (Maybe Integer, Maybe Integer))
find = $$(compile [||\xs -> (L.find (P.>= 8) xs, L.find (P.>= 12) xs)||])

any :: CompiledCode (P.BuiltinList Integer -> (Bool, Bool))
any = $$(compile [||\xs -> (L.any (P.>= 8) xs, L.any (P.>= 12) xs)||])

all :: CompiledCode (P.BuiltinList Integer -> (Bool, Bool))
all = $$(compile [||\xs -> (L.all (P.>= 8) xs, L.all (P.>= 0) xs)||])

index :: CompiledCode (P.BuiltinList Integer -> Integer)
index = $$(compile [||\xs -> xs L.!! 5 ||])

indexNegative :: CompiledCode (P.BuiltinList Integer -> Integer)
indexNegative = $$(compile [||\xs -> xs L.!! (-1) ||])

indexTooLarge :: CompiledCode (P.BuiltinList Integer -> Integer)
indexTooLarge = $$(compile [||\xs -> xs L.!! 10 ||])

cons :: CompiledCode (P.BuiltinList Integer -> P.BuiltinList Integer)
cons = $$(compile [||\xs -> L.cons 0 xs||])

unconsJust :: CompiledCode (P.BuiltinList Integer -> Maybe (Integer, P.BuiltinList Integer))
unconsJust = $$(compile [||\xs -> L.uncons xs||])

unconsNothing :: CompiledCode (P.BuiltinList Integer -> Maybe (Integer, P.BuiltinList Integer))
unconsNothing = $$(compile [||\_ -> L.uncons L.empty||])

-- empty :: CompiledCode (P.BuiltinList Integer -> a)
-- empty = $$(compile [|| L.empty ||])

-- singleton :: CompiledCode (P.BuiltinList Integer -> a)
-- singleton = $$(compile [|| L.singleton ||])

-- null :: CompiledCode (P.BuiltinList Integer -> a)
-- null = $$(compile [|| L.null ||])

-- caseList' :: CompiledCode (P.BuiltinList Integer -> a)
-- caseList' = $$(compile [|| L.caseList' ||])

-- (++) :: CompiledCode (P.BuiltinList Integer -> a)
-- (++) = $$(compile [|| L.(++) ||])

-- (<|) :: CompiledCode (P.BuiltinList Integer -> a)
-- (<|) = $$(compile [|| L.(<|) ||])

-- append :: CompiledCode (P.BuiltinList Integer -> a)
-- append = $$(compile [|| L.append ||])

-- findIndices :: CompiledCode (P.BuiltinList Integer -> a)
-- findIndices = $$(compile [|| L.findIndices ||])

-- filter :: CompiledCode (P.BuiltinList Integer -> a)
-- filter = $$(compile [|| L.filter ||])

-- mapMaybe :: CompiledCode (P.BuiltinList Integer -> a)
-- mapMaybe = $$(compile [|| L.mapMaybe ||])

-- length :: CompiledCode (P.BuiltinList Integer -> a)
-- length = $$(compile [|| L.length ||])

-- and :: CompiledCode (P.BuiltinList Integer -> a)
-- and = $$(compile [|| L.and ||])

-- or :: CompiledCode (P.BuiltinList Integer -> a)
-- or = $$(compile [|| L.or ||])

-- notElem :: CompiledCode (P.BuiltinList Integer -> a)
-- notElem = $$(compile [|| L.notElem ||])

-- foldr :: CompiledCode (P.BuiltinList Integer -> a)
-- foldr = $$(compile [|| L.foldr ||])

-- foldl :: CompiledCode (P.BuiltinList Integer -> a)
-- foldl = $$(compile [|| L.foldl ||])

-- concat :: CompiledCode (P.BuiltinList Integer -> a)
-- concat = $$(compile [|| L.concat ||])

-- concatMap :: CompiledCode (P.BuiltinList Integer -> a)
-- concatMap = $$(compile [|| L.concatMap ||])

-- listToMaybe :: CompiledCode (P.BuiltinList Integer -> a)
-- listToMaybe = $$(compile [|| L.listToMaybe ||])

-- uniqueElement :: CompiledCode (P.BuiltinList Integer -> a)
-- uniqueElement = $$(compile [|| L.uniqueElement ||])

-- revAppend :: CompiledCode (P.BuiltinList Integer -> a)
-- revAppend = $$(compile [|| L.revAppend ||])

-- reverse :: CompiledCode (P.BuiltinList Integer -> a)
-- reverse = $$(compile [|| L.reverse ||])

-- replicate :: CompiledCode (P.BuiltinList Integer -> a)
-- replicate = $$(compile [|| L.replicate ||])

-- findIndex :: CompiledCode (P.BuiltinList Integer -> a)
-- findIndex = $$(compile [|| L.findIndex ||])

-- unzip :: CompiledCode (P.BuiltinList Integer -> a)
-- unzip = $$(compile [|| L.unzip ||])

-- zip :: CompiledCode (P.BuiltinList Integer -> a)
-- zip = $$(compile [|| L.zip ||])

-- zipWith :: CompiledCode (P.BuiltinList Integer -> a)
-- zipWith = $$(compile [|| L.zipWith ||])

-- head :: CompiledCode (P.BuiltinList Integer -> a)
-- head = $$(compile [|| L.head ||])

-- last :: CompiledCode (P.BuiltinList Integer -> a)
-- last = $$(compile [|| L.last ||])

-- tail :: CompiledCode (P.BuiltinList Integer -> a)
-- tail = $$(compile [|| L.tail ||])

-- take :: CompiledCode (P.BuiltinList Integer -> a)
-- take = $$(compile [|| L.take ||])

-- drop :: CompiledCode (P.BuiltinList Integer -> a)
-- drop = $$(compile [|| L.drop ||])

-- dropWhile :: CompiledCode (P.BuiltinList Integer -> a)
-- dropWhile = $$(compile [|| L.dropWhile ||])

-- splitAt :: CompiledCode (P.BuiltinList Integer -> a)
-- splitAt = $$(compile [|| L.splitAt ||])

-- elemBy :: CompiledCode (P.BuiltinList Integer -> a)
-- elemBy = $$(compile [|| L.elemBy ||])

-- partition :: CompiledCode (P.BuiltinList Integer -> a)
-- partition = $$(compile [|| L.partition ||])

-- sort :: CompiledCode (P.BuiltinList Integer -> a)
-- sort = $$(compile [|| L.sort ||])

-- sortBy :: CompiledCode (P.BuiltinList Integer -> a)
-- sortBy = $$(compile [|| L.sortBy ||])

-- nub :: CompiledCode (P.BuiltinList Integer -> a)
-- nub = $$(compile [|| L.nub ||])

-- nubBy :: CompiledCode (P.BuiltinList Integer -> a)
-- nubBy = $$(compile [|| L.nubBy ||])

l :: CompiledCode (P.BuiltinList Integer)
l = liftCodeDef $ toBuiltin ([1 .. 10] :: [Integer])
