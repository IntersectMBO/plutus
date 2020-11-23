-- | A dynamic built-in name test.

{-# OPTIONS_GHC -fno-warn-orphans               #-}
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}

{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Evaluation.DynamicBuiltins.Definition
    ( test_definition
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Generators.Interesting
import           Language.PlutusCore.MkPlc                                  hiding (error)
import           Language.PlutusCore.Pretty

import           Language.PlutusCore.StdLib.Data.Bool
import qualified Language.PlutusCore.StdLib.Data.Function                   as Plc
import qualified Language.PlutusCore.StdLib.Data.List                       as Plc

import           Evaluation.DynamicBuiltins.Common

import           Data.Either
import           Data.Proxy
import           Data.Text.Prettyprint.Doc
import           GHC.Generics
import           GHC.Ix
import           Hedgehog                                                   hiding (Opaque, Size, Var)
import qualified Hedgehog.Gen                                               as Gen
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.Hedgehog

instance (Bounded a, Bounded b) => Bounded (Either a b) where
    minBound = Left  minBound
    maxBound = Right maxBound

size :: forall a. (Bounded a, Enum a) => Int
size = fromEnum (maxBound :: a) - fromEnum (minBound :: a) + 1

-- >>> map fromEnum [Left False .. Right GT]
-- [0,1,2,3,4]
-- >>> map toEnum [0 .. 4] :: [Either Bool Ordering]
-- [Left False,Left True,Right LT,Right EQ,Right GT]
instance (Eq a, Eq b, Bounded a, Bounded b, Enum a, Enum b) => Enum (Either a b) where
    succ (Left x)
        | x == maxBound = Right minBound
        | otherwise     = Left $ succ x
    succ (Right y)
        | y == maxBound = error "Out of bounds"
        | otherwise     = Right $ succ y

    pred (Left x)
        | x == minBound = error "Out of bounds"
        | otherwise     = Left $ pred x
    pred (Right y)
        | y == minBound = Left maxBound
        | otherwise     = Right $ pred y

    toEnum i
        | i < s     = Left  $ toEnum i
        | otherwise = Right $ toEnum (i - s)
        where s = size @a

    fromEnum (Left  x) = fromEnum x
    fromEnum (Right y) = size @a + fromEnum y

-- >>> import GHC.Ix
-- >>> map (unsafeIndex (Left False, Right GT)) [Left False .. Right GT]
-- [0,1,2,3,4]
-- >>> let bounds = (Left (False, EQ), Right (True, GT)) in map (unsafeIndex bounds) $ range bounds
-- [0,1,2,3,4,5,6,7,8,9]
instance (Bounded a, Bounded b, Ix a, Ix b) => Ix (Either a b) where
    range (Right _, Left  _) = []
    range (Right x, Right y) = map Right (range (x, y))
    range (Left  x, Right y) = map Left (range (x, maxBound)) ++ map Right (range (minBound, y))
    range (Left  x, Left  y) = map Left (range (x, y))

    unsafeIndex (Right _, _) (Left  _) = error "Out of bounds"
    unsafeIndex (Left  x, n) (Left  i) = unsafeIndex (x, fromLeft maxBound n) i
    unsafeIndex (Right x, n) (Right i) = unsafeIndex (x, fromRight (error "Out of bounds") n) i
    unsafeIndex (Left  x, n) (Right i) =
        unsafeIndex (x, maxBound) maxBound + 1 +
            unsafeIndex (minBound, fromRight (error "Out of bounds") n) i

    inRange (m, n) i = m <= i && i <= n

data ExtensionFun
    = Factorial
    | Const
    | Id
    | IdFInteger
    | IdList
    | IdRank2
    deriving (Show, Eq, Ord, Enum, Bounded, Ix, Generic, Hashable)
    deriving ExMemoryUsage via (GenericExMemoryUsage ExtensionFun)

instance Pretty ExtensionFun where pretty = viaShow

instance (ToBuiltinMeaning uni fun1, ToBuiltinMeaning uni fun2) =>
            ToBuiltinMeaning uni (Either fun1 fun2) where
    type DynamicPart uni (Either fun1 fun2) = (DynamicPart uni fun1, DynamicPart uni fun2)
    type CostingPart uni (Either fun1 fun2) = (CostingPart uni fun1, CostingPart uni fun2)

    toBuiltinMeaning (Left  fun) = case toBuiltinMeaning fun of
        BuiltinMeaning sch toF toExF -> BuiltinMeaning sch (toF . fst) (toExF . fst)
    toBuiltinMeaning (Right fun) = case toBuiltinMeaning fun of
        BuiltinMeaning sch toF toExF -> BuiltinMeaning sch (toF . snd) (toExF . snd)

defBuiltinsRuntimeExt
    :: HasConstantIn DefaultUni term
    => BuiltinsRuntime (Either DefaultFun ExtensionFun) term
defBuiltinsRuntimeExt = toBuiltinsRuntime (defDefaultFunDyn, ()) (defaultCostModel, ())

data ListRep a
instance KnownTypeAst uni a => KnownTypeAst uni (ListRep a) where
    toTypeAst _ = TyApp () Plc.listTy . toTypeAst $ Proxy @a
type instance ToBinds (ListRep a) = TypeToBinds a

data TyForallStarRep text unique a
instance (KnownTypeAst uni (TyVarRep text unique), KnownTypeAst uni a) =>
            KnownTypeAst uni (TyForallStarRep text unique a) where
    toTypeAst _ = case toTypeAst @uni $ Proxy @(TyVarRep text unique) of
        TyVar () name -> TyForall () name (Type ()) . toTypeAst $ Proxy @a
        _             -> error "Impossible"

instance (GShow uni, GEq uni, uni `Includes` Integer) => ToBuiltinMeaning uni ExtensionFun where
    type DynamicPart uni ExtensionFun = ()
    type CostingPart uni ExtensionFun = ()
    toBuiltinMeaning Factorial = toStaticBuiltinMeaning (\(n :: Integer) -> product [1..n]) mempty
    toBuiltinMeaning Const =
        toStaticBuiltinMeaning
            (const
                :: (a ~ Opaque term (TyVarRep "a" 0), b ~ Opaque term (TyVarRep "b" 1))
                => a -> b -> a)
            mempty
    toBuiltinMeaning Id =
        toStaticBuiltinMeaning
            (Prelude.id :: a ~ Opaque term (TyVarRep "a" 0) => a -> a)
            mempty
    toBuiltinMeaning IdFInteger =
        -- Automatic inference doesn't work with higher-kinded variables, hence doing everything
        -- manually.
        BuiltinMeaning
            (TypeSchemeAll @"f" @0 Proxy (KindArrow () (Type ()) $ Type ()) $ \(_ :: Proxy f) ->
                let ty = Proxy @(Opaque _ (TyAppRep f Integer))
                in ty `TypeSchemeArrow` TypeSchemeResult ty)
            (\_ -> Prelude.id)
            mempty
    toBuiltinMeaning IdList =
        toStaticBuiltinMeaning
            (Prelude.id :: a ~ Opaque term (ListRep (Opaque term (TyVarRep "a" 0))) => a -> a)
            mempty
    toBuiltinMeaning IdRank2 =
        BuiltinMeaning
            (TypeSchemeAll @"f" @0 Proxy (KindArrow () (Type ()) $ Type ()) $ \(_ :: Proxy f) ->
                let ty = Proxy @(Opaque _ (TyForallStarRep "a" 1 (TyAppRep f (Opaque _ (TyVarRep "a" 1)))))
                in ty `TypeSchemeArrow` TypeSchemeResult ty)
            (\_ -> Prelude.id)
            mempty

-- | Check that 'Factorial' from the above computes to the same thing as
-- a factorial defined in PLC itself.
test_Factorial :: TestTree
test_Factorial =
    testCase "Factorial" $ do
        let ten = mkConstant @Integer @DefaultUni () 10
            lhs = typecheckEvaluateCek defBuiltinsRuntimeExt $ Apply () (Builtin () $ Right Factorial) ten
            rhs = typecheckEvaluateCek defBuiltinsRuntimeExt $ Apply () (mapFun Left factorial) ten
        assertBool "type checks" $ isRight lhs
        lhs @?= rhs

-- | Check that 'Const' from the above computes to the same thing as
-- a const defined in PLC itself.
test_Const :: TestTree
test_Const =
    testProperty "Const" . property $ do
        c <- forAll Gen.unicode
        b <- forAll Gen.bool
        let tC = mkConstant () c
            tB = mkConstant () b
            char = toTypeAst @DefaultUni @Char Proxy
            runConst con = mkIterApp () (mkIterInst () con [char, bool]) [tC, tB]
            lhs = typecheckReadKnownCek defBuiltinsRuntimeExt $ runConst $ Builtin () (Right Const)
            rhs = typecheckReadKnownCek defBuiltinsRuntimeExt $ runConst $ mapFun Left Plc.const
        lhs === Right (Right c)
        lhs === rhs

-- | Test that a polymorphic built-in function doesn't subvert the CEK machine.
-- See https://github.com/input-output-hk/plutus/issues/1882
test_Id :: TestTree
test_Id =
    testCase "Id" $ do
        let zer = mkConstant @Integer @DefaultUni () 0
            one = mkConstant @Integer @DefaultUni () 1
            integer = mkTyBuiltin @Integer ()
            -- id {integer -> integer} ((\(i : integer) (j : integer) -> i) 1) 0
            term =
                mkIterApp () (TyInst () (Builtin () $ Right Id) (TyFun () integer integer))
                    [ Apply () constIntegerInteger one
                    , zer
                    ] where
                          constIntegerInteger = runQuote $ do
                              i <- freshName "i"
                              j <- freshName "j"
                              return
                                  . LamAbs () i integer
                                  . LamAbs () j integer
                                  $ Var () i
        typecheckEvaluateCek defBuiltinsRuntimeExt term @?= Right (EvaluationSuccess one)

-- | Test that a polymorphic built-in function can have a higher-kinded type variable in its
-- signature.
test_IdFInteger :: TestTree
test_IdFInteger =
    testCase "IdFInteger" $ do
        let tyAct = typeOfBuiltinFunction @DefaultUni IdFInteger
            tyExp = let f = TyName . Name "f" $ Unique 0
                        fInteger = TyApp () (TyVar () f) $ mkTyBuiltin @Integer ()
                    in TyForall () f (KindArrow () (Type ()) $ Type ()) $ TyFun () fInteger fInteger
            one = mkConstant @Integer @DefaultUni () 1
            ten = mkConstant @Integer @DefaultUni () 10
            res = mkConstant @Integer @DefaultUni () 55
            -- sum (idFInteger {list} (enumFromTo 1 10))
            term
                = Apply () (mapFun Left Plc.sum)
                . Apply () (TyInst () (Builtin () $ Right IdFInteger) Plc.listTy)
                $ mkIterApp () (mapFun Left Plc.enumFromTo) [one, ten]
        tyAct @?= tyExp
        typecheckEvaluateCek defBuiltinsRuntimeExt term @?= Right (EvaluationSuccess res)

test_IdList :: TestTree
test_IdList =
    testCase "IdList" $ do
        let tyAct = typeOfBuiltinFunction @DefaultUni IdList
            tyExp = let a = TyName . Name "a" $ Unique 0
                        listA = TyApp () Plc.listTy (TyVar () a)
                    in TyForall () a (Type ()) $ TyFun () listA listA
            one = mkConstant @Integer @DefaultUni () 1
            ten = mkConstant @Integer @DefaultUni () 10
            res = mkConstant @Integer @DefaultUni () 55
            integer = mkTyBuiltin @Integer ()
            -- sum (idList {integer} (enumFromTo 1 10))
            term
                = Apply () (mapFun Left Plc.sum)
                . Apply () (TyInst () (Builtin () $ Right IdList) integer)
                $ mkIterApp () (mapFun Left Plc.enumFromTo) [one, ten]
        tyAct @?= tyExp
        typecheckEvaluateCek defBuiltinsRuntimeExt term @?= Right (EvaluationSuccess res)

{- Note [Higher-rank built-in functions]
We can't unlift a monomorphic function passed to a built-in function, let alone unlift a polymorphic
one, however we can define a built-in function that accepts an 'Opaque' term of a polymorphic type.
However, as is always the case with an 'Opaque' term, we can't inspect it or use it in any
non-opaque way, so a function of type

    all (f :: * -> *). (all (a :: *). f a) -> all (a :: *). f a

can be assigned the following meaning on the Haskell side:

    \x -> x

but we have no way of providing a meaning for a built-in function with the following signature:

    all (f :: * -> *). all (a :: *). (all (a :: *). f a) -> f a

That's because the meaning function would have to instantiate the @all (a :: *). f a@ argument
somehow to get an @f a@, but that is exactly "using a term in a non-opaque way".

Basically, since we are either generic over @term@ or, like in the example below, use 'CekValue',
there's is no sensible way of instantiating a passed polymorphic argument (or applying a passed
argument when it's a function, for another example).
-}

-- | Test that opaque terms with higher-rank types are allowed.
test_IdRank2 :: TestTree
test_IdRank2 =
    testCase "IdRank2" $ do
        let tyAct = typeOfBuiltinFunction @DefaultUni IdRank2
            tyExp = let f = TyName . Name "f" $ Unique 0
                        a = TyName . Name "a" $ Unique 1
                        allAfA = TyForall () a (Type ()) . TyApp () (TyVar () f) $ TyVar () a
                    in TyForall () f (KindArrow () (Type ()) $ Type ()) $ TyFun () allAfA allAfA
            res = mkConstant @Integer @DefaultUni () 0
            integer = mkTyBuiltin @Integer ()
            -- sum (idRank2 {list} nil {integer})
            term
                = Apply () (mapFun Left Plc.sum)
                . TyInst () (Apply () (TyInst () (Builtin () $ Right IdRank2) Plc.listTy) Plc.nil)
                $ integer
        tyAct @?= tyExp
        typecheckEvaluateCek defBuiltinsRuntimeExt term @?= Right (EvaluationSuccess res)

test_definition :: TestTree
test_definition =
    testGroup "definition"
        [ test_Factorial
        , test_Const
        , test_Id
        , test_IdFInteger
        , test_IdList
        , test_IdRank2
        ]
