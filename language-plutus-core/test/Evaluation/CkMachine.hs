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
    TermOf b bv <- forAllPretty $ genTermLoose TypedBuiltinBool
    TermOf i iv <- forAllPretty $ genTermLoose int
    TermOf j jv <- forAllPretty $ genTermLoose int
    term <- liftIO . runFresh $ do
        builtinConst <- getBuiltinConst
        builtinUnit  <- getBuiltinUnit
        builtinIf    <- getBuiltinIf
        let constSpec k =
                Apply ()
                    (foldl (TyInst ()) builtinConst [TyBuiltin () TyInteger, builtinUnit])
                    k
        return $ foldl (Apply ())
            (TyInst () builtinIf $ TyBuiltin () TyInteger)
            [b, constSpec i, constSpec j]
    case evaluateCk term of
        CkEvalFailure     -> lift $ putStrLn "silly" -- lift . putStrLn $ prettyString term ++ "\n"
        CkEvalSuccess res -> case makeConstant int $ if bv then iv else jv of
            Nothing   -> fail "No way"
            Just res' -> do
                lift $ putStrLn "fine"
                res === res'

main = defaultMain test_ifIntegers
