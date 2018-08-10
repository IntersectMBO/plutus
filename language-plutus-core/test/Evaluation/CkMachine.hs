{-# LANGUAGE OverloadedStrings #-}
module Evaluation.CkMachine where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.CkMachine
import           Evaluation.Constant.GenTypedBuiltin
import           Evaluation.Generator

import           Control.Applicative
import qualified Data.ByteString.Lazy as BSL
import           Control.Monad.Reader
import           Control.Monad.Morph
import           Hedgehog hiding (Size, Var, annotate)
import qualified Hedgehog.Gen   as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty
import           Test.Tasty.Hedgehog

parseRunCk :: BSL.ByteString -> Either ParseError CkEvalResult
parseRunCk = fmap (runCk . void) . parseScoped

-- blah = parseRunCk $ "(program 0.1.0 [(lam x [(con integer) (con 32)] x) (con 32 ! 123456)])"

test_ifIntegers :: TestTree
test_ifIntegers = testProperty "ifIntegers" . property $ do
    size <- forAll genSizeDef
    let int = TypedBuiltinSized (SizeValue size) TypedBuiltinSizedInt
    TermOf b bv <- forAllPretty . genTerm $ TypedBuiltinBool
    TermOf i iv <- forAllPretty $ genTerm int
    TermOf j jv <- forAllPretty $ genTerm int
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
    liftIO $ putStrLn $ prettyString term
    liftIO $ putStrLn $ prettyString $ makeConstant int $ if bv then iv else jv
    case evaluateCk term of
        CkEvalFailure     -> return ()
        CkEvalSuccess res -> case makeConstant int $ if bv then iv else jv of
            Nothing   -> return ()
            Just res' -> res === res'

main = defaultMain test_ifIntegers
