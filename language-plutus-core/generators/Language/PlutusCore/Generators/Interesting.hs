-- | Sample generators used for tests.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeApplications  #-}

module Language.PlutusCore.Generators.Interesting
    ( TermGen
    , genOverapplication
    , factorial
    , applyFactorial
    , genFactorial
    , genNaiveFib
    , genNatRoundtrip
    , natSum
    , genListSum
    , genIfIntegers
    , fromInterestingTermGens
    ) where

import           Language.PlutusCore.Constant
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type

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
type TermGen size a = Gen (TermOf (TypedBuiltinValue size a))

-- | Generates application of a built-in that returns a @boolean@, immediately saturated afterwards.
--
-- > lessThanInteger {integer s1} $i1 $i2 {integer s2} $j1 $j2 == if i1 < i2 then j1 else j2
genOverapplication :: TermGen size Integer
genOverapplication = do
    s1 <- genSizeIn 1 8
    s2 <- genSizeIn 1 8
    let typedInt1 = TypedBuiltinSized (SizeValue s1) TypedBuiltinSizedInt
        typedInt2 = TypedBuiltinSized (SizeValue s2) TypedBuiltinSizedInt
        int2 = typedBuiltinToType typedInt2
    TermOf ti1 i1 <- genTypedBuiltinSmall typedInt1
    TermOf ti2 i2 <- genTypedBuiltinSmall typedInt1
    TermOf tj1 j1 <- genTypedBuiltinSmall typedInt2
    TermOf tj2 j2 <- genTypedBuiltinSmall typedInt2
    let term =
            mkIterApp ()
                (TyInst ()
                    (mkIterApp ()
                        (TyInst ()
                            (builtinNameAsTerm LessThanInteger)
                            (TyInt () s1))
                        [ti1, ti2])
                    int2)
                [tj1, tj2]
        value = TypedBuiltinValue typedInt2 $ if i1 < i2 then j1 else j2
    return $ TermOf term value

-- | @\i -> product [1 :: Integer .. i]@ as a PLC term.
--
-- > /\(s :: size) -> \(i : integer s) ->
--     let ss = sizeOfInteger {s} i in
--         product {s} ss (enumFromTo {s} (resizeInteger {1} {s} ss 1!1) i)
factorial :: Term TyName Name ()
factorial = runQuote $ do
    s <- freshTyName () "s"
    i <- freshName () "i"
    let int = TyApp () (TyBuiltin () TyInteger) $ TyVar () s
        ss  = Apply () (TyInst () (builtinNameAsTerm SizeOfInteger) (TyVar () s)) (Var () i)
    return
        . TyAbs () s (Size ())
        . LamAbs () i int
        . mkIterApp () (TyInst () List.product $ TyVar () s)
        $ [ ss
          , mkIterApp () (TyInst () List.enumFromTo $ TyVar () s)
                [ makeDynBuiltinInt (TyVar () s) ss 1
                , Var () i
                ]
          ]

-- | The naive exponential fibonacci function as a PLC term.
--
-- > /\ (s :: size) -> \(i0 : integer s) ->
-- >     fix {integer s} {integer s}
-- >         (\(rec : integer s -> integer s) (i : integer s) ->
-- >             let ss = sizeOfInteger {s} i in
-- >                 ifThenElse {integer s}
-- >                     (lessThanEqInteger {s} i (resizeInteger {1} {s} ss 1!1))
-- >                     (\(u : unit) -> i)
-- >                     (\(u : unit) -> addInteger {s}
-- >                         (rec (subtractInteger {s} i (resizeInteger {1} {s} ss 1!1)))
-- >                         (rec (subtractInteger {s} i (resizeInteger {1} {s} ss 1!2)))))
-- >         i0
naiveFib :: Term TyName Name ()
naiveFib = runQuote $ do
    s   <- freshTyName () "s"
    i0  <- freshName () "i0"
    rec <- freshName () "rec"
    i   <- freshName () "i"
    u   <- freshName () "u"
    let intS              = TyApp () (TyBuiltin () TyInteger) (TyVar () s)
        builtinNameS name = TyInst () (builtinNameAsTerm name) $ TyVar () s
        makeIntS          = makeDynBuiltinIntSizedAs (TyVar () s) (Var () i)
    return
        . TyAbs () s (Size ())
        . LamAbs () i0 intS
        $ mkIterApp () (mkIterInst () fix [intS, intS])
            [   LamAbs () rec (TyFun () intS intS)
              . LamAbs () i intS
              $ mkIterApp () (TyInst () ifThenElse intS)
                  [ mkIterApp () (builtinNameS LessThanEqInteger)
                      [Var () i, makeIntS 1]
                  , LamAbs () u unit $ Var () i
                  , LamAbs () u unit $ mkIterApp () (builtinNameS AddInteger)
                      [ Apply () (Var () rec) $ mkIterApp () (builtinNameS SubtractInteger)
                          [Var () i, makeIntS 1]
                      , Apply () (Var () rec) $ mkIterApp () (builtinNameS SubtractInteger)
                          [Var () i, makeIntS 2]
                      ]
                  ]
            , Var () i0
            ]

-- | Apply some factorial function to its 'Size' and 'Integer' arguments.
-- This function exist, because we have another implementation via dynamic built-ins
-- and want to compare it to the direct implementation from the above.
applyFactorial :: Term TyName Name () -> Size -> Integer -> Term TyName Name ()
applyFactorial fact sizev iv = Apply () (TyInst () fact size) i where
    i    = Constant () $ BuiltinInt () sizev iv
    size = TyInt () sizev

-- | Generate a term that computes the factorial of an @integer@ and return it
-- along with the factorial of the corresponding 'Integer' computed on the Haskell side.
genFactorial :: TermGen size Integer
genFactorial = do
    let m = 10
        sizev = sizeOfInteger $ Prelude.product [1..m]
        typedIntS = TypedBuiltinSized (SizeValue sizev) TypedBuiltinSizedInt
    iv <- Gen.integral $ Range.linear 1 m
    let term = applyFactorial factorial sizev iv
    return . TermOf term . TypedBuiltinValue typedIntS $ Prelude.product [1..iv]

-- | Generate a term that computes the ith Fibonacci number and return it
-- along with the corresponding 'Integer' computed on the Haskell side.
genNaiveFib :: TermGen size Integer
genNaiveFib = do
    let fibs = scanl (+) 0 $ 1 : fibs
        m = 16
        sizev = sizeOfInteger $ fibs !! 48
        size  = TyInt () sizev
        typedIntS = TypedBuiltinSized (SizeValue sizev) TypedBuiltinSizedInt
    iv <- Gen.integral $ Range.linear 0 m
    let term = Apply () (TyInst () naiveFib size) . Constant () $ BuiltinInt () sizev iv
    return . TermOf term . TypedBuiltinValue typedIntS $ fibs `genericIndex` iv

-- | Generate an 'Integer', turn it into a Scott-encoded PLC @Nat@ (see 'Nat'),
-- turn that @Nat@ into the corresponding PLC @integer@ using a fold (see 'FoldNat')
-- defined in terms of generic fix (see 'Fix') and return the result
-- along with the original 'Integer'
genNatRoundtrip :: TermGen size Integer
genNatRoundtrip = do
    let sizev = 1
        size  = TyInt () sizev
        ssize = Constant () $ BuiltinSize () sizev
        typedIntS = TypedBuiltinSized (SizeValue sizev) TypedBuiltinSizedInt
    TermOf _ iv <- Gen.filter ((>= 0) . _termOfValue) $ genTypedBuiltinDef typedIntS
    let term = mkIterApp () (TyInst () natToInteger size) [ssize, metaIntegerToNat iv]
    return . TermOf term $ TypedBuiltinValue typedIntS iv

-- | @sumNat@ as a PLC term.
natSum :: Size -> Term TyName Name ()
natSum s = runQuote $ do
    let int = TyApp () (TyBuiltin () TyInteger) $ TyInt () s
        nat = _recursiveType natData
        add = TyInst () (Builtin () (BuiltinName () AddInteger)) $ TyInt () s
    acc <- freshName () "acc"
    n <- freshName () "n"
    return
        $ mkIterApp () (mkIterInst () foldList [nat, int])
          [   LamAbs () acc int
            . LamAbs () n nat
            . mkIterApp () add
            $ [ Var () acc
              , mkIterApp () (TyInst () natToInteger (TyInt () s))
                  [ Constant () $ BuiltinSize () s
                  , Var () n
                  ]
              ]
          , Constant () $ BuiltinInt () s 0
          ]

-- | Generate a list of 'Integer's, turn it into a Scott-encoded PLC @List@ (see 'List'),
-- sum elements of the list (see 'Sum') and return it along with the sum of the original list.
genListSum :: TermGen size Integer
genListSum = do
    size <- genSizeIn 1 8
    let typedIntS = TypedBuiltinSized (SizeValue size) TypedBuiltinSizedInt
        intS = typedBuiltinToType typedIntS
    ps <- Gen.list (Range.linear 0 10) $ genTypedBuiltinSmall typedIntS
    let list = metaListToList intS $ map _termOfTerm ps
        term = mkIterApp () (TyInst () List.sum $ TyInt () size)
            [ Constant () $ BuiltinSize () size
            , list
            ]
    let haskSum = Prelude.sum $ map _termOfValue ps
    return . TermOf term $ TypedBuiltinValue typedIntS haskSum

-- | Generate a @boolean@ and two @integer@s and check whether @if b then i1 else i2@
-- means the same thing in Haskell and PLC. Terms are generated using 'genTermLoose'.
genIfIntegers :: TermGen size Integer
genIfIntegers = do
    size <- genSizeDef
    let typedIntS = TypedBuiltinSized (SizeValue size) TypedBuiltinSizedInt
        intS = typedBuiltinToType typedIntS
    TermOf b bv <- genTermLoose $ TypedBuiltinDyn @Bool
    TermOf i iv <- genTermLoose typedIntS
    TermOf j jv <- genTermLoose typedIntS
    let instConst = Apply () $ mkIterInst () Function.const [intS, unit]
        value = if bv then iv else jv
        term =
            mkIterApp ()
                (TyInst () ifThenElse intS)
                [b, instConst i, instConst j]
    return . TermOf term $ TypedBuiltinValue typedIntS value

-- | Apply a function to all interesting generators and collect the results.
fromInterestingTermGens :: (forall a. String -> TermGen size a -> c) -> [c]
fromInterestingTermGens f =
    [ f "overapplication" genOverapplication
    , f "factorial"       genFactorial
    , f "fibonacci"       genNaiveFib
    , f "NatRoundTrip"    genNatRoundtrip
    , f "ListSum"         genListSum
    , f "IfIntegers"      genIfIntegers
    ]
