{-# LANGUAGE OverloadedStrings #-}
module Evaluation.CkMachine
    ( test_ifIntegers
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.CkMachine
import           Evaluation.Constant.TypedBuiltinGen
import           Evaluation.Generator

import qualified Data.ByteString.Lazy as BSL
import           Control.Monad.Reader
import           Control.Monad.Morph
import           Hedgehog hiding (Size, Var, annotate)
import           Test.Tasty
import           Test.Tasty.Hedgehog

parseRunCk :: BSL.ByteString -> Either ParseError CkEvalResult
parseRunCk = fmap (runCk . void) . parseScoped

-- blah = parseRunCk $ "(program 0.1.0 [(lam x [(con integer) (con 32)] x) (con 32 ! 123456)])"

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
        let constSpec k =
                Apply ()
                    (foldl (TyInst ()) builtinConst [TyBuiltin () TyInteger, builtinUnit])
                    k
        let term = foldl (Apply ())
                (TyInst () builtinIf $ TyBuiltin () TyInteger)
                [b, constSpec i, constSpec j]
            value = if bv then iv else jv
        return $ TermOf term value
    case evaluateCk term of
        CkEvalFailure     -> return ()
        CkEvalSuccess res -> case makeConstant int value of
            Nothing   -> fail "ifIntegers: value out of bounds"
            Just res' -> do liftIO $ putStrLn $ prettyString term ++ "\n"; res === res'

main = defaultMain test_ifIntegers
