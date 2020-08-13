-- | Sample generators used for tests.

{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Language.PlutusCore.Generators.Interesting
    ( TermGen
    , TermOf(..)
    , genOverapplication
    , factorial
    , genFactorial
    , naiveFib
    , genNaiveFib
    , genNatRoundtrip
    , natSum
    , genListSum
    , genIfIntegers
    , fromInterestingTermGens
    ) where

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Universe

import           Language.PlutusCore.StdLib.Data.Bool
import           Language.PlutusCore.StdLib.Data.Function as Function
import           Language.PlutusCore.StdLib.Data.List     as List
import           Language.PlutusCore.StdLib.Data.Nat
import           Language.PlutusCore.StdLib.Data.Unit
import           Language.PlutusCore.StdLib.Meta
import           Language.PlutusCore.StdLib.Type

import           Language.PlutusCore.Generators

import           Data.List                                (genericIndex)
import           Hedgehog                                 hiding (Size, Var)
import qualified Hedgehog.Gen                             as Gen
import qualified Hedgehog.Range                           as Range

-- | The type of terms-and-their-values generators.
type TermGen uni a = Gen (TermOf (Term TyName Name uni ()) a)

-- | Generates application of a builtin that returns a function, immediately saturated afterwards.
--
-- > ifThenElse {integer -> integer -> integer} (lessThanInteger i j) addInteger subtractInteger i j
-- >     == if i < j then i + j else i - j
genOverapplication :: Generatable uni => TermGen uni Integer
genOverapplication = do
    let typedInteger = AsKnownType
        integer = toTypeAst typedInteger
    TermOf ti i <- genTypedBuiltinDef typedInteger
    TermOf tj j <- genTypedBuiltinDef typedInteger
    let term =
            mkIterApp ()
                (TyInst () (staticBuiltinNameAsTerm IfThenElse) . TyFun () integer $ TyFun () integer integer)
                [ mkIterApp () (staticBuiltinNameAsTerm LessThanInteger) [ti, tj]
                , staticBuiltinNameAsTerm AddInteger
                , staticBuiltinNameAsTerm SubtractInteger
                , ti
                , tj
                ]
    return . TermOf term $ if i < j then i + j else i - j

-- | @\i -> product [1 :: Integer .. i]@ as a PLC term.
--
-- > \(i : integer) -> product (enumFromTo 1 i)
factorial :: uni `IncludesAll` '[Integer, (), Bool] => Term TyName Name uni ()
factorial = runQuote $ do
    i <- freshName "i"
    let int = mkTyBuiltin @Integer ()
    return
        . LamAbs () i int
        . mkIterApp () List.product
        $ [ mkIterApp () List.enumFromTo [ mkConstant @Integer () 1 , Var () i]]

-- | The naive exponential fibonacci function as a PLC term.
--
-- > \(i0 : integer) ->
-- >     fix {integer} {integer}
-- >         (\(rec : integer -> integer) (i : integer) ->
-- >                 ifThenElse {integer}
-- >                     (lessThanEqInteger i 1)
-- >                     (\(u : unit) -> i)
-- >                     (\(u : unit) -> addInteger
-- >                         (rec (subtractInteger i 1))
-- >                         (rec (subtractInteger i 2)))
-- >         i0
naiveFib :: uni `IncludesAll` '[Integer, (), Bool] => Integer -> Term TyName Name uni ()
naiveFib iv = runQuote $ do
    i0  <- freshName "i0"
    rec <- freshName "rec"
    i   <- freshName "i"
    u   <- freshName "u"
    let
      intS = mkTyBuiltin @Integer ()
      fib = LamAbs () i0 intS
        $ mkIterApp () (mkIterInst () fix [intS, intS])
            [   LamAbs () rec (TyFun () intS intS)
              . LamAbs () i intS
              $ mkIterApp () (TyInst () ifThenElse intS)
                  [ mkIterApp () (staticBuiltinNameAsTerm LessThanEqInteger)
                      [Var () i, mkConstant @Integer () 1]
                  , LamAbs () u unit $ Var () i
                  , LamAbs () u unit $ mkIterApp () (staticBuiltinNameAsTerm AddInteger)
                      [ Apply () (Var () rec) $ mkIterApp () (staticBuiltinNameAsTerm SubtractInteger)
                          [Var () i, mkConstant @Integer () 1]
                      , Apply () (Var () rec) $ mkIterApp () (staticBuiltinNameAsTerm SubtractInteger)
                          [Var () i, mkConstant @Integer () 2]
                      ]
                  ]
            , Var () i0
            ]
    pure . Apply () fib $ mkConstant @Integer () iv

-- | Generate a term that computes the factorial of an @integer@ and return it
-- along with the factorial of the corresponding 'Integer' computed on the Haskell side.
genFactorial :: uni `IncludesAll` '[Integer, (), Bool] => TermGen uni Integer
genFactorial = do
    let m = 10
    iv <- Gen.integral $ Range.linear 1 m
    let term = Apply () factorial (mkConstant @Integer () iv)
    return . TermOf term $ Prelude.product [1..iv]

-- | Generate a term that computes the ith Fibonacci number and return it
-- along with the corresponding 'Integer' computed on the Haskell side.
genNaiveFib :: uni `IncludesAll` '[Integer, (), Bool] => TermGen uni Integer
genNaiveFib = do
    let fibs = scanl (+) 0 $ 1 : fibs
        m = 16
    iv <- Gen.integral $ Range.linear 0 m
    return . TermOf (naiveFib iv) $ fibs `genericIndex` iv

-- | Generate an 'Integer', turn it into a Scott-encoded PLC @Nat@ (see 'Nat'),
-- turn that @Nat@ into the corresponding PLC @integer@ using a fold (see 'FoldNat')
-- defined in terms of generic fix (see 'Fix') and return the result
-- along with the original 'Integer'
genNatRoundtrip
    :: forall uni. Generatable uni => TermGen uni Integer
genNatRoundtrip = do
    let typedInt = AsKnownType @(Term TyName Name uni ())
    TermOf _ iv <- Gen.filter ((>= 0) . _termOfValue) $ genTypedBuiltinDef typedInt
    let term = mkIterApp () natToInteger [metaIntegerToNat iv]
    return $ TermOf term iv

-- | @sumNat@ as a PLC term.
natSum :: uni `Includes` Integer => Term TyName Name uni ()
natSum = runQuote $ do
    let int = mkTyBuiltin @Integer ()
        nat = _recursiveType natData
        add = staticBuiltinNameAsTerm AddInteger
    acc <- freshName "acc"
    n <- freshName "n"
    return
        $ mkIterApp () (mkIterInst () foldList [nat, int])
          [   LamAbs () acc int
            . LamAbs () n nat
            . mkIterApp () add
            $ [ Var () acc
              , mkIterApp () natToInteger [ Var () n ]
              ]
          , mkConstant @Integer () 0
          ]

-- | Generate a list of 'Integer's, turn it into a Scott-encoded PLC @List@ (see 'List'),
-- sum elements of the list (see 'Sum') and return it along with the sum of the original list.
genListSum :: Generatable uni => TermGen uni Integer
genListSum = do
    let typedInt = AsKnownType
        intS = toTypeAst typedInt
    ps <- Gen.list (Range.linear 0 10) $ genTypedBuiltinDef typedInt
    let list = metaListToList intS $ Prelude.map _termOfTerm ps
        term = mkIterApp () List.sum [list]
    let haskSum = Prelude.sum $ Prelude.map _termOfValue ps
    return $ TermOf term haskSum

-- | Generate a @boolean@ and two @integer@s and check whether @if b then i1 else i2@
-- means the same thing in Haskell and PLC. Terms are generated using 'genTermLoose'.
genIfIntegers :: Generatable uni => TermGen uni Integer
genIfIntegers = do
    let typedInt = AsKnownType
        int = toTypeAst typedInt
    TermOf b bv <- genTermLoose AsKnownType
    TermOf i iv <- genTermLoose typedInt
    TermOf j jv <- genTermLoose typedInt
    let instConst = Apply () $ mkIterInst () Function.const [int, unit]
        value = if bv then iv else jv
        term =
            mkIterApp ()
                (TyInst () ifThenElse int)
                [b, instConst i, instConst j]
    return $ TermOf term value

-- | Check that builtins can be partially applied.
genApplyAdd1 :: Generatable uni => TermGen uni Integer
genApplyAdd1 = do
    let typedInt = AsKnownType
        int = toTypeAst typedInt
    TermOf i iv <- genTermLoose typedInt
    TermOf j jv <- genTermLoose typedInt
    let term =
            mkIterApp () (mkIterInst () applyFun [int, int])
                [ Apply () (staticBuiltinNameAsTerm AddInteger) i
                , j
                ]
    return . TermOf term $ iv + jv

-- | Check that builtins can be partially applied.
genApplyAdd2 :: Generatable uni => TermGen uni Integer
genApplyAdd2 = do
    let typedInt = AsKnownType
        int = toTypeAst typedInt
    TermOf i iv <- genTermLoose typedInt
    TermOf j jv <- genTermLoose typedInt
    let term =
            mkIterApp () (mkIterInst () applyFun [int, TyFun () int int])
                [ staticBuiltinNameAsTerm AddInteger
                , i
                , j
                ]
    return . TermOf term $ iv + jv

-- | Check that division by zero results in 'Error'.
genDivideByZero :: Generatable uni => TermGen uni (EvaluationResult Integer)
genDivideByZero = do
    op <- Gen.element [DivideInteger, QuotientInteger, ModInteger, RemainderInteger]
    TermOf i _ <- genTermLoose $ AsKnownType @_ @Integer
    let term = mkIterApp () (staticBuiltinNameAsTerm op) [i, mkConstant @Integer () 0]
    return $ TermOf term EvaluationFailure

-- | Check that division by zero results in 'Error' even if a function doesn't use that argument.
genDivideByZeroDrop :: Generatable uni => TermGen uni (EvaluationResult Integer)
genDivideByZeroDrop = do
    op <- Gen.element [DivideInteger, QuotientInteger, ModInteger, RemainderInteger]
    let typedInt = AsKnownType
        int = toTypeAst typedInt
    TermOf i iv <- genTermLoose typedInt
    let term =
            mkIterApp () (mkIterInst () Function.const [int, int])
                [ mkIterApp () (staticBuiltinNameAsTerm op) [i, mkConstant @Integer () 0]
                , mkConstant @Integer () iv
                ]
    return $ TermOf term EvaluationFailure

-- | Apply a function to all interesting generators and collect the results.
fromInterestingTermGens
    :: Generatable uni
    => (forall a. KnownType (Term TyName Name uni ()) a => String -> TermGen uni a -> c) -> [c]
fromInterestingTermGens f =
    [ f "overapplication"  genOverapplication
    , f "factorial"        genFactorial
    , f "fibonacci"        genNaiveFib
    , f "NatRoundTrip"     genNatRoundtrip
    , f "ListSum"          genListSum
    , f "IfIntegers"       genIfIntegers
    , f "ApplyAdd1"        genApplyAdd1
    , f "ApplyAdd2"        genApplyAdd2
    , f "DivideByZero"     genDivideByZero
    , f "DivideByZeroDrop" genDivideByZeroDrop
    ]
