module Main where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Coolean
import Control.Monad.Except
import Language.PlutusCore.PropTest
import Language.PlutusCore
import Data.Either

import MAlonzo.Code.Main (checkKindAgda)
import MAlonzo.Code.Scoped (deBruijnifyK)

import Language.PlutusCore.DeBruijn
import Raw


main :: IO ()
main = defaultMain allTests

allTests :: TestTree
allTests = testGroup "all tests" [ testCaseCount "soundness" test ]

testCaseCount :: String -> IO Integer -> TestTree
testCaseCount name act = testCaseInfo name $
  liftM (\i -> show i ++ " types generated") act


-- NEAT settings

depth :: Int
depth = 10

kind :: Kind ()
kind = Type ()

-- |Check if the type/kind checker or generation threw any errors.
isSafe :: ExceptT (ErrorP a) Quote a -> Cool
isSafe = toCool . isRight . runQuote . runExceptT

prop_checkKindSound :: TyProp
prop_checkKindSound k _ tyQ = isSafe $ do
  ty <- withExceptT GenErrorP tyQ
  ty <- withExceptT FVErrorP $ deBruijnTy ty
  withExceptT TypeErrorP $ case checkKindAgda (AlexPn 0 0 0 <$ ty) (deBruijnifyK (convK k)) of
    Just _ -> return ()
    Nothing -> throwError undefined

test :: IO Integer
test = testTyProp depth kind prop_checkKindSound

