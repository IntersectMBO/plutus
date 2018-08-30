{-# LANGUAGE OverloadedStrings #-}
module Evaluation.CkMachine
    ( test_evaluateCk
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.CkMachine
import           Language.PlutusCore.Constant
import           Language.PlutusCore.StdLib.Data.Bool
import           Language.PlutusCore.StdLib.Data.Function
import           Language.PlutusCore.StdLib.Data.List
import           Language.PlutusCore.StdLib.Data.Nat
import           Language.PlutusCore.StdLib.Data.Unit
import           Language.PlutusCore.TestSupport
import           PlutusPrelude                            hiding (hoist, list)

import           Control.Monad.Morph
import           Data.Foldable
import           Hedgehog                                 hiding (Size, Var)
import qualified Hedgehog.Gen                             as Gen
import qualified Hedgehog.Range                           as Range
import           Test.Tasty
import           Test.Tasty.Hedgehog

-- TODO: also type check the terms.

-- | Convert an 'Integer' to a @nat@.
getBuiltinIntegerToNat :: Integer -> Quote (Term TyName Name ())
getBuiltinIntegerToNat n
    | n < 0     = error $ "getBuiltinIntegerToNat: negative argument: " ++ show n
    | otherwise = go n where
          go 0 = getBuiltinZero
          go m = Apply () <$> getBuiltinSucc <*> go (m - 1)

-- | Convert a @nat@ to an 'Integer'.
getBuiltinNatToInteger :: Natural -> Term TyName Name () -> Quote (Term TyName Name ())
getBuiltinNatToInteger s n = do
    builtinFoldNat <- getBuiltinFoldNat
    let int = Constant () . BuiltinInt () s
    return
        . foldl (Apply ()) (TyInst () builtinFoldNat $ TyBuiltin () TyInteger)
        $ [ Apply () (Constant () $ BuiltinName () AddInteger) $ int 1
          , int 0
          , n
          ]

-- | Generate an 'Integer', turn it into a Scott-encoded PLC @Nat@ (see 'getBuiltinNat'),
-- turn that @Nat@ into the corresponding PLC @integer@ using a fold (see 'getBuiltinFoldNat')
-- defined in terms of generic fix (see 'getBuiltinFix'), feed the resulting 'Term' to the CK machine
-- (see 'evaluateCk') and check that the original 'Integer' and the computed @integer@ are in sync.
test_NatRoundtrip :: TestTree
test_NatRoundtrip = testProperty "NatRoundtrip" . property $ do
    let size = 1
        int1 = TypedBuiltinSized (SizeValue size) TypedBuiltinSizedInt
    TermOf n nv <- forAllPrettyCfg . Gen.filter ((>= 0) . _termOfValue) $ genTypedBuiltinDef int1
    let term = runQuote $ getBuiltinIntegerToNat nv >>= getBuiltinNatToInteger size
    evaluateCk term === CkEvalSuccess n

getListToBuiltinList :: Type TyName () -> [Term TyName Name ()] -> Quote (Term TyName Name ())
getListToBuiltinList ty ts = do
    builtinNil  <- getBuiltinNil
    builtinCons <- getBuiltinCons
    return $ foldr
        (\x xs -> foldl (Apply ()) (TyInst () builtinCons ty) [x, xs])
        (TyInst () builtinNil ty)
        ts

-- | Generate a list of 'Integer's, turn it into a Scott-encoded PLC @List@ (see 'getBuiltinList'),
-- sum elements of the list (see 'getBuiltinSum'), feed the resulting 'Term' to the CK machine
-- (see 'evaluateCk') and check that 'sum' applied to the original list is in sync with the computed sum.
test_ListSum :: TestTree
test_ListSum = testProperty "ListSum" . property $ do
    size <- forAll $ genSizeIn 1 8
    let intSized      = TyBuiltin () TyInteger
        typedIntSized = TypedBuiltinSized (SizeValue size) TypedBuiltinSizedInt
    ps <- forAllPrettyCfg . Gen.list (Range.linear 0 10) $ genTypedBuiltinLoose typedIntSized
    let term = runQuote $ do
            builtinSum <- getBuiltinSum size
            list <- getListToBuiltinList intSized $ map _termOfTerm ps
            return $ Apply () builtinSum list
        haskSum   = sum $ map _termOfValue ps
        mayPlcSum = runQuote . makeBuiltin $ TypedBuiltinValue typedIntSized haskSum
    for_ mayPlcSum $ \plcSum -> evaluateCk term === CkEvalSuccess plcSum

-- | Generate a @boolean@ and two @integer@s and check whether
-- @if b then i1 else i2@ means the same thing in Haskell and PLC.
-- Terms are generated using 'genTermLoose'.
test_ifIntegers :: TestTree
test_ifIntegers = testProperty "ifIntegers" . property $ do
    size <- forAll genSizeDef
    let int = TypedBuiltinSized (SizeValue size) TypedBuiltinSizedInt
    TermOf term value <- hoist (return . runQuote) $ do
        TermOf b bv <- forAllPrettyCfgT $ genTermLoose TypedBuiltinBool
        TermOf i iv <- forAllPrettyCfgT $ genTermLoose int
        TermOf j jv <- forAllPrettyCfgT $ genTermLoose int
        builtinConst <- lift getBuiltinConst
        builtinUnit  <- lift getBuiltinUnit
        builtinIf    <- lift getBuiltinIf
        let builtinConstSpec =
                Apply () $ foldl (TyInst ()) builtinConst [TyBuiltin () TyInteger, builtinUnit]
            term = foldl (Apply ())
                (TyInst () builtinIf $ TyBuiltin () TyInteger)
                [b, builtinConstSpec i, builtinConstSpec j]
            value = if bv then iv else jv
        return $ TermOf term value
    case evaluateCk term of
        CkEvalFailure     -> return ()
        CkEvalSuccess res -> res === unsafeMakeBuiltin (TypedBuiltinValue int value)

test_evaluateCk :: TestTree
test_evaluateCk = testGroup "evaluateCk"
    [ test_NatRoundtrip
    , test_ListSum
    , test_ifIntegers
    ]
