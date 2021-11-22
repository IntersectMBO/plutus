{-# OPTIONS_GHC -fno-warn-orphans               #-}
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}

{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module PlutusCore.Examples.Builtins where

import PlutusCore
import PlutusCore.Constant
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Pretty

import PlutusCore.StdLib.Data.ScottList qualified as Plc

import Control.Exception
import Data.Either
import Data.Hashable (Hashable)
import Data.Kind qualified as GHC (Type)
import Data.Proxy
import Data.Tuple
import Data.Void
import GHC.Generics
import GHC.Ix
import Prettyprinter

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

-- See Note [Representable built-in functions over polymorphic built-in types]
data ExtensionFun
    = Factorial
    | Const
    | Id
    | IdFInteger
    | IdList
    | IdRank2
    -- The next four are for testing that costing always precedes actual evaluation.
    | FailingSucc
    | ExpensiveSucc
    | FailingPlus
    | ExpensivePlus
    | Undefined
    | Absurd
    | ErrorPrime  -- Like 'Error', but a builtin. What do we even need 'Error' for at this point?
                  -- Who knows what machinery a tick could break, hence the @Prime@ part.
    | Comma
    | BiconstPair  -- A safe version of 'Comma' as discussed in
                   -- Note [Representable built-in functions over polymorphic built-in types].
    | Swap  -- For checking that permuting type arguments of a polymorphic built-in works correctly.
    | SwapEls  -- For checking that nesting polymorphic built-in types and instantiating them with
               -- a mix of monomorphic types and type variables works correctly.
    deriving (Show, Eq, Ord, Enum, Bounded, Ix, Generic, Hashable)

instance Pretty ExtensionFun where pretty = viaShow

instance (ToBuiltinMeaning uni fun1, ToBuiltinMeaning uni fun2) =>
            ToBuiltinMeaning uni (Either fun1 fun2) where
    type CostingPart uni (Either fun1 fun2) = (CostingPart uni fun1, CostingPart uni fun2)

    toBuiltinMeaning (Left  fun) = case toBuiltinMeaning fun of
        BuiltinMeaning sch toF toExF -> BuiltinMeaning sch toF (toExF . fst)
    toBuiltinMeaning (Right fun) = case toBuiltinMeaning fun of
        BuiltinMeaning sch toF toExF -> BuiltinMeaning sch toF (toExF . snd)

defBuiltinsRuntimeExt
    :: HasConstantIn DefaultUni term
    => BuiltinsRuntime (Either DefaultFun ExtensionFun) term
defBuiltinsRuntimeExt = toBuiltinsRuntime (defaultBuiltinCostModel, ())

data PlcListRep (a :: GHC.Type)
instance KnownTypeAst uni a => KnownTypeAst uni (PlcListRep a) where
    type ToBinds (PlcListRep a) = ToBinds a

    toTypeAst _ = TyApp () Plc.listTy . toTypeAst $ Proxy @a

instance KnownTypeAst DefaultUni Void where
    toTypeAst _ = runQuote $ do
        a <- freshTyName "a"
        pure $ TyForall () a (Type ()) $ TyVar () a
instance UniOf term ~ DefaultUni => KnownTypeIn DefaultUni term Void where
    makeKnown _ _ = absurd
    readKnown mayCause _ = throwingWithCause _UnliftingError "Can't unlift a 'Void'" mayCause

data BuiltinErrorCall = BuiltinErrorCall
    deriving (Show, Eq, Exception)

-- See Note [Representable built-in functions over polymorphic built-in types].
-- We have lists in the universe and so we can define a function like @\x -> [x, x]@ that duplicates
-- the constant that it receives. Should memory consumption of that function be linear in the number
-- of duplicates that the function creates? I think, no:
--
-- 1. later we can call @head@ over the resulting list thus not duplicating anything in the end
-- 2. any monomorphic builtin touching a duplicated constant will automatically
--    add it to the current budget. And if we never touch the duplicate again and just keep it
--    around, then it won't ever increase memory consumption. And any other node will be taken into
--    account automatically as well: just think that having @\x -> f x x@ as a PLC term is supposed
--    to be handled correctly by design
instance uni ~ DefaultUni => ToBuiltinMeaning uni ExtensionFun where
    type CostingPart uni ExtensionFun = ()
    toBuiltinMeaning :: forall term. HasConstantIn uni term => ExtensionFun -> BuiltinMeaning term ()

    toBuiltinMeaning Factorial =
        makeBuiltinMeaning
            (\(n :: Integer) -> product [1..n])
            mempty  -- Whatever.

    toBuiltinMeaning Const =
        makeBuiltinMeaning
            const
            (\_ _ _ -> ExBudget 1 0)

    toBuiltinMeaning Id =
        makeBuiltinMeaning
            Prelude.id
            (\_ _ -> ExBudget 1 0)

    toBuiltinMeaning IdFInteger =
        makeBuiltinMeaning
            (Prelude.id
                :: a ~ Opaque term (TyAppRep (TyVarRep ('TyNameRep "f" 0)) Integer)
                => a -> a)
            (\_ _ -> ExBudget 1 0)

    toBuiltinMeaning IdList =
        makeBuiltinMeaning
            (Prelude.id
                :: a ~ Opaque term (PlcListRep (TyVarRep ('TyNameRep "a" 0)))
                => a -> a)
            (\_ _ -> ExBudget 1 0)

    toBuiltinMeaning IdRank2 =
        makeBuiltinMeaning
            (Prelude.id
                :: ( f ~ 'TyNameRep "f" 0
                   , a ~ 'TyNameRep @GHC.Type "a" 1
                   , afa ~ Opaque term (TyForallRep a (TyAppRep (TyVarRep f) (TyVarRep a)))
                   )
                => afa -> afa)
            (\_ _ -> ExBudget 1 0)

    toBuiltinMeaning FailingSucc =
        makeBuiltinMeaning
            @(Integer -> Integer)
            (\_ -> throw BuiltinErrorCall)
            (\_ _ -> ExBudget 1 0)

    toBuiltinMeaning ExpensiveSucc =
        makeBuiltinMeaning
            @(Integer -> Integer)
            (\_ -> throw BuiltinErrorCall)
            (\_ _ -> unExRestrictingBudget enormousBudget)

    toBuiltinMeaning FailingPlus =
        makeBuiltinMeaning
            @(Integer -> Integer -> Integer)
            (\_ _ -> throw BuiltinErrorCall)
            (\_ _ _ -> ExBudget 1 0)

    toBuiltinMeaning ExpensivePlus =
        makeBuiltinMeaning
            @(Integer -> Integer -> Integer)
            (\_ _ -> throw BuiltinErrorCall)
            (\_ _ _ -> unExRestrictingBudget enormousBudget)

    toBuiltinMeaning Undefined =
        makeBuiltinMeaning
            undefined
            (\_ -> ExBudget 1 0)

    toBuiltinMeaning Absurd =
        makeBuiltinMeaning
            absurd
            (\_ _ -> ExBudget 1 0)

    toBuiltinMeaning ErrorPrime =
        makeBuiltinMeaning
            EvaluationFailure
            (\_ -> ExBudget 1 0)

    toBuiltinMeaning Comma = makeBuiltinMeaning commaPlc mempty where
        commaPlc
            :: SomeConstant uni a
            -> SomeConstant uni b
            -> SomeConstantPoly uni (,) '[a, b]
        commaPlc (SomeConstant (Some (ValueOf uniA x))) (SomeConstant (Some (ValueOf uniB y))) =
            SomeConstantPoly $ someValueOf (DefaultUniPair uniA uniB) (x, y)

    toBuiltinMeaning BiconstPair = makeBuiltinMeaning biconstPairPlc mempty where
        biconstPairPlc
            :: SomeConstant uni a
            -> SomeConstant uni b
            -> SomeConstantPoly uni (,) '[a, b]
            -> EvaluationResult (SomeConstantPoly uni (,) '[a, b])
        biconstPairPlc
            (SomeConstant (Some (ValueOf uniA x)))
            (SomeConstant (Some (ValueOf uniB y)))
            (SomeConstantPoly (Some (ValueOf uniPairAB _))) = do
                DefaultUniPair uniA' uniB' <- pure uniPairAB
                Just Refl <- pure $ uniA `geq` uniA'
                Just Refl <- pure $ uniB `geq` uniB'
                pure . SomeConstantPoly $ someValueOf uniPairAB (x, y)

    toBuiltinMeaning Swap = makeBuiltinMeaning swapPlc mempty where
        swapPlc
            :: SomeConstantPoly uni (,) '[a, b]
            -> EvaluationResult (SomeConstantPoly uni (,) '[b, a])
        swapPlc (SomeConstantPoly (Some (ValueOf uniPairAB p))) = do
            DefaultUniPair uniA uniB <- pure uniPairAB
            pure . SomeConstantPoly $ someValueOf (DefaultUniPair uniB uniA) (snd p, fst p)

    toBuiltinMeaning SwapEls = makeBuiltinMeaning swapElsPlc mempty where
        -- The type reads as @[(a, Bool)] -> [(Bool, a)]@.
        swapElsPlc
            :: a ~ Opaque term (TyVarRep ('TyNameRep "a" 0))
            => SomeConstantPoly uni [] '[SomeConstantPoly uni (,) '[a, Bool]]
            -> EvaluationResult (SomeConstantPoly uni [] '[SomeConstantPoly uni (,) '[Bool, a]])
        swapElsPlc (SomeConstantPoly (Some (ValueOf uniList xs))) = do
            DefaultUniList (DefaultUniPair uniA DefaultUniBool) <- pure uniList
            let uniList' = DefaultUniList $ DefaultUniPair DefaultUniBool uniA
            pure . SomeConstantPoly . someValueOf uniList' $ map swap xs
