{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS -fplugin Language.PlutusTx.Plugin -fplugin-opt Language.PlutusTx.Plugin:defer-errors -fplugin-opt Language.PlutusTx.Plugin:strip-context #-}
-- the simplifier messes with things otherwise
{-# OPTIONS_GHC   -O0 #-}
{-# OPTIONS_GHC   -Wno-orphans #-}
{-# OPTIONS_GHC   -fmax-simplifier-iterations=0 #-}  -- being paranoid
-- this adds source notes which helps the plugin give better errors
{-# OPTIONS_GHC   -g #-}

module Plugin.ReadValue
    ( readDyns
    ) where


import           Language.PlutusTx.Code
import           Language.PlutusTx.Plugin

import qualified Language.PlutusCore                        as PLC
import qualified Language.PlutusCore.Constant               as PLC
import qualified Language.PlutusCore.Constant.Dynamic       as PLC
import qualified Language.PlutusCore.Interpreter.CekMachine as PLC

import           Test.Tasty
import           Test.Tasty.HUnit

-- this module does lots of weird stuff deliberately
{-# ANN module ("HLint: ignore"::String) #-}

newtype MyNewtype = MyNewtype Int
    deriving (Show, Eq)

data MyMonoRecord = MyMonoRecord { mrA :: Int , mrB :: Int}
    deriving (Show, Eq)

data MyMonoData = Mono1 Int Int | Mono2 Int | Mono3 Int
    deriving (Show, Eq)

-- | Convert a Plutus Core term into a Haskell value of type @a@ and inject it into the type @b@
-- using a provided injection function. The intermediate type @a@ is needed, because right now we
-- can only read values as explicit sums of products (i.e. 'Either's of '(,)'s) and can't supply
-- constructors of Haskell data types as arguments to Plutus Core terms in order to get Haskell
-- values directly without going through some generic representation.
readCompiledCode :: PLC.KnownDynamicBuiltinType a => (a -> b) -> CompiledCode b -> b
readCompiledCode inj compiled =
    case PLC.readDynamicBuiltinCek mempty term of
        Right (PLC.EvaluationSuccess x) -> inj x
        Left _                          -> error "Can't read compiled code"
  where
    PLC.Program _ _ term = getPlc compiled

readMyMonoRecord :: CompiledCode MyMonoRecord -> MyMonoRecord
readMyMonoRecord = readCompiledCode (uncurry MyMonoRecord)

myMonoRecord01 :: MyMonoRecord
myMonoRecord01 = MyMonoRecord 0 1

compiledMyMonoRecord01 :: CompiledCode MyMonoRecord
compiledMyMonoRecord01 = plc @"compiledMyMonoRecord01" (MyMonoRecord 0 1)

readMyMonoRecords :: CompiledCode [MyMonoRecord] -> [MyMonoRecord]
readMyMonoRecords = readCompiledCode (Prelude.map (uncurry MyMonoRecord) . PLC.unPlcList)

myMonoRecords :: [MyMonoRecord]
myMonoRecords = Prelude.zipWith MyMonoRecord [0..4] [1..5]

compiledMyMonoRecords :: CompiledCode [MyMonoRecord]
compiledMyMonoRecords = plc @"compiledMyMonoRecords" (
        [MyMonoRecord 0 1, MyMonoRecord 1 2, MyMonoRecord 2 3, MyMonoRecord 3 4, MyMonoRecord 4 5]
    )

toMyMonoData :: Either (Int, Int) (Either Int Int) -> MyMonoData
toMyMonoData (Left  (i, j)   ) = Mono1 i j
toMyMonoData (Right (Left  i)) = Mono2 i
toMyMonoData (Right (Right i)) = Mono3 i

readMyMonoDatas :: CompiledCode [MyMonoData] -> [MyMonoData]
readMyMonoDatas = readCompiledCode (Prelude.map toMyMonoData . PLC.unPlcList)

myMonoDatas :: [MyMonoData]
myMonoDatas = [Mono2 2, Mono1 0 1, Mono1 4 3, Mono3 5, Mono2 8, Mono1 6 7]

compiledMyMonoDatas :: CompiledCode [MyMonoData]
compiledMyMonoDatas = plc @"compiledMyMonoDatas" (
        [Mono2 2, Mono1 0 1, Mono1 4 3, Mono3 5, Mono2 8, Mono1 6 7]
    )

data MyMonoData2 = Mono21 Int Int | Mono22 Int
    deriving (Show, Eq)

toMyMonoData2 :: Either (Int, Int) Int -> MyMonoData2
toMyMonoData2 (Left  (i, j)) = Mono21 i j
toMyMonoData2 (Right i     ) = Mono22 i

readMyMonoData2 :: CompiledCode MyMonoData2 -> MyMonoData2
readMyMonoData2 = readCompiledCode toMyMonoData2

myMono21 :: MyMonoData2
myMono21 = Mono21 0 1

myMono22 :: MyMonoData2
myMono22 = Mono22 2

compiledMyMono21 :: CompiledCode MyMonoData2
compiledMyMono21 = plc @"compiledMyMono21" (Mono21 0 1)

compiledMyMono22 :: CompiledCode MyMonoData2
compiledMyMono22 = plc @"compiledMyMono22" (Mono22 2)

readMyMonoData2s :: CompiledCode [MyMonoData2] -> [MyMonoData2]
readMyMonoData2s = readCompiledCode (Prelude.map toMyMonoData2 . PLC.unPlcList)

myMonoData2s :: [MyMonoData2]
myMonoData2s = [Mono22 2, Mono21 0 1, Mono21 4 3, Mono22 8, Mono21 6 7]

compiledMyMonoData2s :: CompiledCode [MyMonoData2]
compiledMyMonoData2s = plc @"compiledMyMonoData2s" (
        [Mono22 2, Mono21 0 1, Mono21 4 3, Mono22 8, Mono21 6 7]
    )

data MyMonoData3 = Mono31 Int | Mono32 Int
    deriving (Show, Eq)

toMyMonoData3 :: Either Int Int -> MyMonoData3
toMyMonoData3 (Left  i) = Mono31 i
toMyMonoData3 (Right i) = Mono32 i

readMyMonoData3 :: CompiledCode MyMonoData3 -> MyMonoData3
readMyMonoData3 = readCompiledCode toMyMonoData3

myMono31 :: MyMonoData3
myMono31 = Mono31 0

myMono32 :: MyMonoData3
myMono32 = Mono32 2

compiledMyMono31 :: CompiledCode MyMonoData3
compiledMyMono31 = plc @"compiledMyMono31" (Mono31 0)

compiledMyMono32 :: CompiledCode MyMonoData3
compiledMyMono32 = plc @"compiledMyMono32" (Mono32 2)

readMyMonoData3s :: CompiledCode [MyMonoData3] -> [MyMonoData3]
readMyMonoData3s = readCompiledCode (Prelude.map toMyMonoData3 . PLC.unPlcList)

myMonoData3s :: [MyMonoData3]
myMonoData3s = [Mono31 2, Mono31 0, Mono31 4, Mono32 8, Mono31 6]

compiledMyMonoData3s :: CompiledCode [MyMonoData3]
compiledMyMonoData3s = plc @"compiledMyMonoData3s" (
        [Mono31 2, Mono31 0, Mono31 4, Mono32 8, Mono31 6]
    )

-- data MyMonoData = Mono1 Int Int | Mono2 Int | Mono3 Int

-- This gives this error:
-- >      error: undefined reference to 'PluginziSpec_MyNewtype_closure'
-- >     |
-- > 427 | readMyNewtype = readCompiledCode MyNewtype
-- readMyNewtype :: CompiledCode MyNewtype -> MyNewtype
-- readMyNewtype = readCompiledCode MyNewtype

myNewtype42 :: MyNewtype
myNewtype42 = MyNewtype 42

compiledMyNewtype42 :: CompiledCode MyNewtype
compiledMyNewtype42 = plc @"myNewtype42" (MyNewtype 42)

readDyns :: TestTree
readDyns = testGroup "reads" [
    testCase "readMyMonoRecord" $ readMyMonoRecord compiledMyMonoRecord01 @?= myMonoRecord01
    , testCase "readMyMonoRecords" $ readMyMonoRecords compiledMyMonoRecords @?= myMonoRecords
    -- All of these result in "Can't read compiled code".
    -- The reason for this is that a constructor carrying two arguments does not compile to
    -- a full product type when there are several constructors.
    -- I.e. `data D = C1 A B | C2` compiles to `all r. (A -> B -> r) -> r -> r`, but we attempt to
    -- read it as `all r1. ((all r2. A -> B -> r2) -> r2) -> r1 -> r1`.
    -- , testCase "readMyMonoDatas" $ readMyMonoDatas compiledMyMonoDatas @?= myMonoDatas
    -- , testCase "readMyMono21" $ readMyMonoData2 compiledMyMono21 @?= myMono21
    -- , testCase "readMyMono22" $ readMyMonoData2 compiledMyMono22 @?= myMono22
    -- , testCase "readMyMonoData2s" $ readMyMonoData2s compiledMyMonoData2s @?= myMonoData2s
    , testCase "readMyMono31" $ readMyMonoData3 compiledMyMono31 @?= myMono31
    , testCase "readMyMono32" $ readMyMonoData3 compiledMyMono32 @?= myMono32
    , testCase "readMyMonoData3s" $ readMyMonoData3s compiledMyMonoData3s @?= myMonoData3s
    -- , testCase "readNewtypeInt" $ readMyNewtype compiledMyNewtype42 @?= myNewtype42
    ]
