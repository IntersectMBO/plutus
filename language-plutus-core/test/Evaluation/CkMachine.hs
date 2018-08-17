{-# LANGUAGE OverloadedStrings #-}
module Evaluation.CkMachine
    ( test_NatRoundtrip
    , test_ifIntegers
    ) where

import           PlutusPrelude
import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.CkMachine
import           Evaluation.Constant.TypedBuiltinGen
import           Evaluation.Generator
import           Evaluation.Terms

import           Control.Monad.Reader
import           Control.Monad.Morph
import           Hedgehog hiding (Size, Var, annotate)
import qualified Hedgehog.Gen as Gen
import           Test.Tasty
import           Test.Tasty.Hedgehog

-- parseRunCk :: BSL.ByteString -> Either ParseError CkEvalResult
-- parseRunCk = fmap (runCk . void) . parseScoped

getBuiltinIntegerToNat :: Integer -> Fresh (Term TyName Name ())
getBuiltinIntegerToNat n
    | n < 0     = error $ "getBuiltinIntegerToNat: negative argument: " ++ show n
    | otherwise = go n where
          go 0 = getBuiltinZero
          go m = Apply () <$> getBuiltinSucc <*> go (m - 1)

getBuiltinNatToInteger :: Natural -> Term TyName Name () -> Fresh (Term TyName Name ())
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
test_NatRoundtrip = testProperty "NatRoundTrip" . property $ do
    let size = 1
        int2 = TypedBuiltinSized (SizeValue size) TypedBuiltinSizedInt
    TermOf n nv <- forAllPretty . Gen.filter ((>= 0) . _termOfValue) $ genTypedBuiltinDef int2
    term <- liftIO . runFresh $ getBuiltinIntegerToNat nv >>= getBuiltinNatToInteger size
    evaluateCk term === CkEvalSuccess n

test_ifIntegers :: TestTree
test_ifIntegers = testProperty "ifIntegers" . property $ do
    size <- forAll genSizeDef
    let int = TypedBuiltinSized (SizeValue size) TypedBuiltinSizedInt
    TermOf term value <- hoist runFresh $ do
        TermOf b bv <- forAllPrettyT $ genTermLoose TypedBuiltinBool
        TermOf i iv <- forAllPrettyT $ genTermLoose int
        TermOf j jv <- forAllPrettyT $ genTermLoose int
        builtinConst <- lift getBuiltinConst
        builtinUnit  <- lift getBuiltinUnit
        builtinIf    <- lift getBuiltinIf
        let builtinConstSpec k =
                Apply ()
                    (foldl (TyInst ()) builtinConst [TyBuiltin () TyInteger, builtinUnit])
                    k
        let term = foldl (Apply ())
                (TyInst () builtinIf $ TyBuiltin () TyInteger)
                [b, builtinConstSpec i, builtinConstSpec j]
            value = if bv then iv else jv
        return $ TermOf term value
    case evaluateCk term of
        CkEvalFailure     -> return ()
        CkEvalSuccess res -> case unsafeMakeConstant int value of
            Nothing   -> fail "ifIntegers: value out of bounds"
            Just res' -> res === res'

-- main = defaultMain test_NatRoundtrip
