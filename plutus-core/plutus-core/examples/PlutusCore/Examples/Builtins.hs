{-# OPTIONS_GHC -fno-warn-orphans               #-}
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}

{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module PlutusCore.Examples.Builtins where

import PlutusCore
import PlutusCore.Builtin
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Pretty

import PlutusCore.StdLib.Data.ScottList qualified as Plc

import Control.Exception
import Data.Default.Class
import Data.Either
import Data.Hashable (Hashable)
import Data.Kind qualified as GHC (Type)
import Data.Proxy
import Data.Some.GADT qualified as GADT
import Data.Tuple
import Data.Void
import GHC.Generics
import GHC.Ix
import GHC.TypeLits
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
    | ForallFortyTwo  -- A builtin for @42 :: forall a. Integer@.
    | SumInteger
    | Const
    | Id
    | IdAssumeBool
    | IdAssumeCheckBool
    | IdSomeConstantBool
    | IdIntegerAsBool
    | IdFInteger
    | IdList
    | IdRank2
    | ScottToMetaUnit
    -- The next four are for testing that costing always precedes actual evaluation.
    | FailingSucc
    | ExpensiveSucc
    | FailingPlus
    | ExpensivePlus
    | IsConstant
    | UnsafeCoerce
    | UnsafeCoerceEl
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
    | ExtensionVersion -- Reflect the version of the Extension
    deriving stock (Show, Eq, Ord, Enum, Bounded, Ix, Generic)
    deriving anyclass (Hashable)

instance Pretty ExtensionFun where pretty = viaShow

instance (ToBuiltinMeaning uni fun1, ToBuiltinMeaning uni fun2
         , Default (BuiltinVersion fun1), Default (BuiltinVersion fun2)
         ) => ToBuiltinMeaning uni (Either fun1 fun2) where

    type CostingPart uni (Either fun1 fun2) = (CostingPart uni fun1, CostingPart uni fun2)

    data BuiltinVersion (Either fun1 fun2) = PairV (BuiltinVersion fun1) (BuiltinVersion fun2)
    toBuiltinMeaning (PairV verL _) (Left  fun) = case toBuiltinMeaning verL fun of
        BuiltinMeaning tySch toF denot ->
            BuiltinMeaning tySch toF (denot . fst)
    toBuiltinMeaning (PairV _ verR) (Right fun) = case toBuiltinMeaning verR fun of
        BuiltinMeaning tySch toF denot ->
            BuiltinMeaning tySch toF (denot . snd)

instance (Default (BuiltinVersion fun1), Default (BuiltinVersion fun2))
         => Default (BuiltinVersion (Either fun1 fun2)) where
    def = PairV def def

-- | Normally @forall@ in the type of a Haskell function gets detected and instantiated
-- automatically, however there's no way of doing that for a @forall@ that binds a never referenced
-- type variable. Which is OK, because that would be a pretty weird builtin, however it's definable
-- and for the purpose of testing we do introduce such a builtin, hence this definition allowing us
-- to create an @all@ that binds a never referenced type variable in Plutus while still using
-- 'makeBuiltinMeaning'.
newtype MetaForall name a = MetaForall a
instance
        ( name ~ 'TyNameRep @kind text uniq, KnownSymbol text, KnownNat uniq
        , KnownKind kind, KnownTypeAst uni a
        ) => KnownTypeAst uni (MetaForall name a) where
    type IsBuiltin (MetaForall name a) = 'False
    type ToHoles (MetaForall name a) = '[TypeHole a]
    type ToBinds (MetaForall name a) = Merge '[ 'GADT.Some name ] (ToBinds a)
    toTypeAst _ = toTypeAst $ Proxy @a
instance MakeKnownIn DefaultUni term a => MakeKnownIn DefaultUni term (MetaForall name a) where
    makeKnown (MetaForall x) = makeKnown x
-- 'ReadKnownIn' doesn't make sense for 'MetaForall'.

data PlcListRep (a :: GHC.Type)
instance KnownTypeAst uni a => KnownTypeAst uni (PlcListRep a) where
    type IsBuiltin (PlcListRep a) = 'False
    type ToHoles (PlcListRep a) = '[RepHole a]
    type ToBinds (PlcListRep a) = ToBinds a
    toTypeAst _ = TyApp () Plc.listTy . toTypeAst $ Proxy @a

instance KnownTypeAst DefaultUni Void where
    toTypeAst _ = runQuote $ do
        a <- freshTyName "a"
        pure $ TyForall () a (Type ()) $ TyVar () a
instance UniOf term ~ DefaultUni => MakeKnownIn DefaultUni term Void where
    makeKnown = absurd
instance UniOf term ~ DefaultUni => ReadKnownIn DefaultUni term Void where
    readKnown _ = throwing _UnliftingError "Can't unlift to 'Void'"

data BuiltinErrorCall = BuiltinErrorCall
    deriving stock (Show, Eq)
    deriving anyclass (Exception)

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

    data BuiltinVersion ExtensionFun = ExtensionFunV0 | ExtensionFunV1

    toBuiltinMeaning :: forall val. HasMeaningIn uni val
                     => BuiltinVersion ExtensionFun
                     -> ExtensionFun
                     -> BuiltinMeaning val ()

    toBuiltinMeaning _ver Factorial =
        makeBuiltinMeaning
            (\(n :: Integer) -> product [1..n])
            mempty  -- Whatever.

    toBuiltinMeaning _ver ForallFortyTwo =
        makeBuiltinMeaning
            forallFortyTwo
            (\_ -> ExBudget 1 0)
      where
        forallFortyTwo :: MetaForall ('TyNameRep @GHC.Type "a" 0) Integer
        forallFortyTwo = MetaForall 42

    toBuiltinMeaning _ver SumInteger =
        makeBuiltinMeaning
            (sum :: [Integer] -> Integer)
            mempty  -- Whatever.

    toBuiltinMeaning _ver Const =
        makeBuiltinMeaning
            const
            (\_ _ _ -> ExBudget 1 0)

    toBuiltinMeaning _ver Id =
        makeBuiltinMeaning
            Prelude.id
            (\_ _ -> ExBudget 1 0)

    toBuiltinMeaning _ver IdAssumeBool =
        makeBuiltinMeaning
            (Prelude.id :: Opaque val Bool -> Opaque val Bool)
            (\_ _ -> ExBudget 1 0)

    toBuiltinMeaning _ver IdAssumeCheckBool =
        makeBuiltinMeaning
            idAssumeCheckBoolPlc
            mempty  -- Whatever.
      where
        idAssumeCheckBoolPlc :: Opaque val Bool -> EvaluationResult Bool
        idAssumeCheckBoolPlc val =
            case asConstant val of
                Right (Some (ValueOf DefaultUniBool b)) -> EvaluationSuccess b
                _                                       -> EvaluationFailure

    toBuiltinMeaning _ver IdSomeConstantBool =
        makeBuiltinMeaning
            idSomeConstantBoolPlc
            mempty  -- Whatever.
      where
        idSomeConstantBoolPlc :: SomeConstant uni Bool -> EvaluationResult Bool
        idSomeConstantBoolPlc = \case
            SomeConstant (Some (ValueOf DefaultUniBool b)) -> EvaluationSuccess b
            _                                              -> EvaluationFailure

    toBuiltinMeaning _ver IdIntegerAsBool =
        makeBuiltinMeaning
            idIntegerAsBool
            mempty  -- Whatever.
      where
        idIntegerAsBool :: SomeConstant uni Integer -> EvaluationResult (SomeConstant uni Integer)
        idIntegerAsBool = \case
            con@(SomeConstant (Some (ValueOf DefaultUniBool _))) -> EvaluationSuccess con
            _                                                    -> EvaluationFailure

    toBuiltinMeaning _ver IdFInteger =
        makeBuiltinMeaning
            (Prelude.id :: fi ~ Opaque val (f `TyAppRep` Integer) => fi -> fi)
            (\_ _ -> ExBudget 1 0)

    toBuiltinMeaning _ver IdList =
        makeBuiltinMeaning
            (Prelude.id :: la ~ Opaque val (PlcListRep a) => la -> la)
            (\_ _ -> ExBudget 1 0)

    toBuiltinMeaning _ver IdRank2 =
        makeBuiltinMeaning
            (Prelude.id
                :: afa ~ Opaque val (TyForallRep @GHC.Type a (TyVarRep f `TyAppRep` TyVarRep a))
                => afa -> afa)
            (\_ _ -> ExBudget 1 0)

    toBuiltinMeaning _ver ScottToMetaUnit =
        makeBuiltinMeaning
            ((\_ -> ())
                -- @(->)@ switches from the Rep context to the Type one. We could make @(->)@
                -- preserve the current context, but there's no such notion in the current
                -- elaboration machinery and we'd better not complicate it further just for the sake
                -- of tests looking a bit nicer. Instead we simply wrap the 'TyVarRep' with 'Opaque'
                -- (unlike in the case of @IdRank2@ where 'TyAppRep' preserves the Rep context).
                :: oa ~ Opaque val (TyVarRep a)
                => Opaque val (TyForallRep a (oa -> oa)) -> ())
            (\_ _ -> ExBudget 1 0)

    toBuiltinMeaning _ver FailingSucc =
        makeBuiltinMeaning
            @(Integer -> Integer)
            (\_ -> throw BuiltinErrorCall)
            (\_ _ -> ExBudget 1 0)

    toBuiltinMeaning _ver ExpensiveSucc =
        makeBuiltinMeaning
            @(Integer -> Integer)
            (\_ -> throw BuiltinErrorCall)
            (\_ _ -> unExRestrictingBudget enormousBudget)

    toBuiltinMeaning _ver FailingPlus =
        makeBuiltinMeaning
            @(Integer -> Integer -> Integer)
            (\_ _ -> throw BuiltinErrorCall)
            (\_ _ _ -> ExBudget 1 0)

    toBuiltinMeaning _ver ExpensivePlus =
        makeBuiltinMeaning
            @(Integer -> Integer -> Integer)
            (\_ _ -> throw BuiltinErrorCall)
            (\_ _ _ -> unExRestrictingBudget enormousBudget)

    toBuiltinMeaning _ver IsConstant =
        makeBuiltinMeaning
            isConstantPlc
            mempty  -- Whatever.
      where
        -- The type signature is just for clarity, it's not required.
        isConstantPlc :: Opaque val a -> Bool
        isConstantPlc = isRight . asConstant

    toBuiltinMeaning _ver UnsafeCoerce =
        makeBuiltinMeaning
            unsafeCoercePlc
            (\_ _ -> ExBudget 1 0)
      where
        -- The type signature is just for clarity, it's not required.
        unsafeCoercePlc :: Opaque val a -> Opaque val b
        unsafeCoercePlc = Opaque . unOpaque

    toBuiltinMeaning _ver UnsafeCoerceEl =
        makeBuiltinMeaning
            unsafeCoerceElPlc
            (\_ _ -> ExBudget 1 0)
      where
        unsafeCoerceElPlc
            :: SomeConstant DefaultUni [a]
            -> EvaluationResult (SomeConstant DefaultUni [b])
        unsafeCoerceElPlc (SomeConstant (Some (ValueOf uniList xs))) = do
            DefaultUniList _ <- pure uniList
            pure $ fromValueOf uniList xs

    toBuiltinMeaning _ver Undefined =
        makeBuiltinMeaning
            undefined
            (\_ -> ExBudget 1 0)

    toBuiltinMeaning _ver Absurd =
        makeBuiltinMeaning
            absurd
            (\_ _ -> ExBudget 1 0)

    toBuiltinMeaning _ver ErrorPrime =
        makeBuiltinMeaning
            EvaluationFailure
            (\_ -> ExBudget 1 0)

    toBuiltinMeaning _ver Comma = makeBuiltinMeaning commaPlc mempty where
        commaPlc
            :: SomeConstant uni a
            -> SomeConstant uni b
            -> SomeConstant uni (a, b)
        commaPlc (SomeConstant (Some (ValueOf uniA x))) (SomeConstant (Some (ValueOf uniB y))) =
            fromValueOf (DefaultUniPair uniA uniB) (x, y)

    toBuiltinMeaning _ver BiconstPair = makeBuiltinMeaning biconstPairPlc mempty where
        biconstPairPlc
            :: SomeConstant uni a
            -> SomeConstant uni b
            -> SomeConstant uni (a, b)
            -> EvaluationResult (SomeConstant uni (a, b))
        biconstPairPlc
            (SomeConstant (Some (ValueOf uniA x)))
            (SomeConstant (Some (ValueOf uniB y)))
            (SomeConstant (Some (ValueOf uniPairAB _))) = do
                DefaultUniPair uniA' uniB' <- pure uniPairAB
                Just Refl <- pure $ uniA `geq` uniA'
                Just Refl <- pure $ uniB `geq` uniB'
                pure $ fromValueOf uniPairAB (x, y)

    toBuiltinMeaning _ver Swap = makeBuiltinMeaning swapPlc mempty where
        swapPlc
            :: SomeConstant uni (a, b)
            -> EvaluationResult (SomeConstant uni (b, a))
        swapPlc (SomeConstant (Some (ValueOf uniPairAB p))) = do
            DefaultUniPair uniA uniB <- pure uniPairAB
            pure $ fromValueOf (DefaultUniPair uniB uniA) (snd p, fst p)

    toBuiltinMeaning _ver SwapEls = makeBuiltinMeaning swapElsPlc mempty where
        -- The type reads as @[(a, Bool)] -> [(Bool, a)]@.
        swapElsPlc
            :: SomeConstant uni [SomeConstant uni (a, Bool)]
            -> EvaluationResult (SomeConstant uni [SomeConstant uni (Bool, a)])
        swapElsPlc (SomeConstant (Some (ValueOf uniList xs))) = do
            DefaultUniList (DefaultUniPair uniA DefaultUniBool) <- pure uniList
            let uniList' = DefaultUniList $ DefaultUniPair DefaultUniBool uniA
            pure . fromValueOf uniList' $ map swap xs

    -- A dummy builtin to reflect the builtin-version of the 'ExtensionFun'.
    -- See Note [Versioned builtins]
    toBuiltinMeaning ver ExtensionVersion =
        makeBuiltinMeaning
        @(() -> EvaluationResult Integer)
        (\(_ :: ()) -> EvaluationSuccess $ case ver of
                ExtensionFunV0 -> 0
                ExtensionFunV1 -> 1
        )
        mempty  -- Whatever

instance Default (BuiltinVersion ExtensionFun) where
    def = ExtensionFunV1
