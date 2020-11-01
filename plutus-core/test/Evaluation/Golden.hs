{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Evaluation.Golden
    ( test_golden
    ) where

import           Prelude                                    hiding (even)

import           Language.PlutusCore.StdLib.Data.Bool
import           Language.PlutusCore.StdLib.Data.Function
import           Language.PlutusCore.StdLib.Data.List
import           Language.PlutusCore.StdLib.Data.Nat
import           Language.PlutusCore.StdLib.Meta
import           Language.PlutusCore.StdLib.Meta.Data.Tuple
import           Language.PlutusCore.StdLib.Type

import           Language.PlutusCore
import           Language.PlutusCore.Evaluation.Machine.Cek
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import           Language.PlutusCore.Generators.Interesting
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Pretty

import           Control.Monad.Except
import qualified Data.ByteString.Lazy                       as BSL
import           Data.Text.Encoding                         (encodeUtf8)
import           Test.Tasty
import           Test.Tasty.Golden

-- (con integer)
integer :: Type TyName DefaultUni ()
integer = mkTyBuiltin @ Integer ()

-- (con string)
string :: Type TyName DefaultUni ()
string = mkTyBuiltin @ String ()

evenAndOdd :: uni `Includes` Bool => Tuple (Term TyName Name uni) uni ()
evenAndOdd = runQuote $ do
    let nat = _recursiveType natData

    evenn <- freshName "even"
    oddd  <- freshName "odd"

    let eoFunc b recc = do
          n <- freshName "n"
          pure $
              LamAbs () n nat $
              Apply () (Apply () (TyInst () (Unwrap () (Var () n)) bool) b) $ Var () recc

    evenF <- FunctionDef () evenn (FunctionType () nat bool) <$> eoFunc true oddd
    oddF  <- FunctionDef () oddd  (FunctionType () nat bool) <$> eoFunc false evenn

    getMutualFixOf () (fixN 2 fixBy) [evenF, oddF]

even :: uni `Includes` Bool => Term TyName Name uni ()
even = runQuote $ tupleTermAt () 0 evenAndOdd

evenAndOddList :: Tuple (Term TyName Name uni) uni ()
evenAndOddList = runQuote $ do
    let list = _recursiveType listData
        nat  = _recursiveType natData
        listNat = TyApp () list nat

    evenn <- freshName "even"
    oddd  <- freshName "odd"

    let eoFunc recc = do
          l <- freshName "l"
          pure $
              LamAbs () l listNat $
              Apply () (
                  Apply () (TyInst () (Unwrap () (Var () l)) listNat)
                  (TyInst() nil nat))
              recc

    evenF <- FunctionDef () evenn (FunctionType () listNat listNat) <$> do
        h <- freshName "head"
        t <- freshName "tail"
        eoFunc $
            LamAbs () h nat $
            LamAbs () t listNat $
            Apply () (Apply () (TyInst () cons nat) (Var () h)) $
            Apply () (Var () oddd) (Var () t)

    oddF <- FunctionDef () oddd (FunctionType () listNat listNat) <$> do
        h <- freshName "head"
        t <- freshName "tail"
        eoFunc $
            LamAbs () h nat $
            LamAbs () t listNat $
            Apply () (Var () evenn) (Var () t)

    getMutualFixOf () (fixN 2 fixBy) [evenF, oddF]

evenList :: Term TyName Name uni ()
evenList = runQuote $ tupleTermAt () 0 evenAndOddList

smallNatList :: Term TyName Name uni ()
smallNatList = metaListToList nat nats where
    nats = Prelude.map metaIntegerToNat [1,2,3]
    nat = _recursiveType natData

polyError :: Term TyName Name uni ()
polyError = runQuote $ do
    a <- freshTyName "a"
    pure $ TyAbs () a (Type ()) $ Error () (TyVar () a)

-- | For checking that evaluating a term to a non-constant results in all remaining variables
-- being instantiated.
closure :: uni `Includes` Integer => Term TyName Name uni ()
closure = runQuote $ do
    i <- freshName "i"
    j <- freshName "j"
    let integer' = mkTyBuiltin @Integer ()
    pure
        . Apply () (LamAbs () i integer' . LamAbs () j integer' $ Var () i)
        $ mkConstant @Integer () 1

goldenVsPretty :: PrettyPlc a => String -> ExceptT BSL.ByteString IO a -> TestTree
goldenVsPretty name value =
    goldenVsString name ("test/Evaluation/Golden/" ++ name ++ ".plc.golden") $
        either id (BSL.fromStrict . encodeUtf8 . render . prettyPlcClassicDebug) <$> runExceptT value

goldenVsEvaluated :: String -> Term TyName Name DefaultUni () -> TestTree
goldenVsEvaluated name = goldenVsPretty name . pure . unsafeEvaluateCek mempty defaultCostModel


-- Tests for evaluation of builtins, mainly checking that interleaving of term
-- and type arguments is correct.  At the moment the only polymorphic builtin
-- we have is ifThenElse.

-- Various components that we'll use to build larger terms for testing

lte :: Term TyName Name DefaultUni ()
lte = staticBuiltinNameAsTerm LessThanEqInteger

eleven :: Term TyName Name DefaultUni ()
eleven = mkConstant @Integer () 11

twentytwo :: Term TyName Name DefaultUni ()
twentytwo = mkConstant @Integer () 22

string1 :: Term TyName Name DefaultUni ()
string1 = mkConstant @String () "11 <= 22"

string2 :: Term TyName Name DefaultUni ()
string2 = mkConstant @String () "¬(11 <= 22)"

-- 11 <= 22
lteExpr :: Term TyName Name DefaultUni ()
lteExpr = mkIterApp () lte [eleven, twentytwo]

-- (builtin ifThenElse)
ite :: Term TyName Name DefaultUni ()
ite = staticBuiltinNameAsTerm IfThenElse

-- { (builtin ifThenElse) (con integer) }
iteAtInteger :: Term TyName Name DefaultUni ()
iteAtInteger = TyInst () ite integer

-- { (builtin ifThenElse) (con string) }
iteAtString :: Term TyName Name DefaultUni ()
iteAtString = TyInst () ite string

-- { (builtin ifThenElse) (forall a . a -> a) }
-- Evaluation should succeed, but typechecking should fail.
-- You're not allowed to instantiate a builtin at a higher kind.
iteAtHigherKind :: Term TyName Name DefaultUni ()
iteAtHigherKind = TyInst () ite (TyForall () a (Type ()) aArrowA)
    where a = TyName (Name "a" (Unique (-1)))
          aArrowA = TyFun () (TyVar () a) (TyVar () a)

-- {ifThenElse @ String} (11<=22): should succeed
iteTest1String :: Term TyName Name DefaultUni ()
iteTest1String = Apply () iteAtString lteExpr

-- {ifThenElse @ String} (11<=22): should succeed
iteTest1Integer :: Term TyName Name DefaultUni ()
iteTest1Integer = Apply () iteAtInteger lteExpr

-- ifThenElse (11<=22): should fail because ifThenElse isn't instantiated
-- Type expcted, term supplied
iteTestUninstantiated :: Term TyName Name DefaultUni ()
iteTestUninstantiated  = Apply () ite lteExpr

-- {ifThenElse @ String} (11<=22) "11 <= 22" "¬(11<=22)": should succeed
iteTest3 :: Term TyName Name DefaultUni ()
iteTest3 = mkIterApp () iteTest1String [string1, string2]

-- {ifThenElse @ Integer} (11<=22) "11 <= 22" "¬(11<=22)": should also succeed.
-- However it's ill-typed: at execution we only check that type instantiations
-- and term arguments are correctly interleaved, not that instantiations are
-- correct.
iteTest4 :: Term TyName Name DefaultUni ()
iteTest4 = mkIterApp () iteTest1Integer [string1, string2]

-- { {ifThenElse @ Integer} @ Integer }: should fail
iteTest5 :: Term TyName Name DefaultUni ()
iteTest5 = TyInst () iteAtInteger integer

-- { [{ifThenElse @ Integer} (11<=22)] @ String }: should fail:
-- term expected, type supplied
iteTest6 :: Term TyName Name DefaultUni ()
iteTest6 = TyInst () iteTest1Integer string

-- TODO: ideally, we want to test this for all the machines.
test_golden :: TestTree
test_golden = testGroup "golden"
    [ goldenVsEvaluated "even2" $ Apply () even $ metaIntegerToNat 2
    , goldenVsEvaluated "even3" $ Apply () even $ metaIntegerToNat 3
    , goldenVsEvaluated "evenList" $ Apply () natSum $ Apply () evenList smallNatList
    , goldenVsEvaluated "polyError" polyError
    , goldenVsEvaluated "polyErrorInst" $ TyInst () polyError (mkTyBuiltin @Integer ())
    , goldenVsEvaluated "closure" closure
    , goldenVsEvaluated "ite" $ ite
    , goldenVsEvaluated "iteAtInteger" $ iteAtInteger
    , goldenVsEvaluated "iteAtString" $ iteAtString
    , goldenVsEvaluated "iteAtHigherKind" $ iteAtHigherKind
    , goldenVsEvaluated "iteTest1Integer" $ iteTest1Integer
    , goldenVsEvaluated "iteTest3" $ iteTest3
    , goldenVsEvaluated "iteTest4" $ iteTest4
    , goldenVsEvaluated "iteTest5" $ iteTest5
    , goldenVsEvaluated "iteTest6" $ iteTest6
    , goldenVsEvaluated "iteTestUninstantiated" $ iteTestUninstantiated
    ]
