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
import PlutusCore.Data
import PlutusCore.Evaluation.Machine.BuiltinCostModel
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.ExBudgetStream
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Pretty

import PlutusCore.StdLib.Data.ScottList qualified as Plc

import Control.Concurrent.MVar
import Control.Exception
import Control.Monad
import Data.Default.Class
import Data.Either
import Data.Kind qualified as GHC (Type)
import Data.Proxy
import Data.Some.GADT qualified as GADT
import Data.Tuple
import Data.Void
import GHC.Generics
import GHC.Ix
import GHC.TypeLits
import Prettyprinter
import System.IO.Unsafe (unsafeInterleaveIO, unsafePerformIO)
import System.Mem (performMinorGC)
import System.Mem.Weak (addFinalizer)

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
    | TrackCosts  -- For checking that each cost is released and can be picked up by GC once it's
                  -- accounted for in the evaluator.
    deriving stock (Show, Eq, Ord, Enum, Bounded, Ix, Generic)
    deriving anyclass (Hashable)

instance Pretty ExtensionFun where pretty = viaShow

instance (ToBuiltinMeaning uni fun1, ToBuiltinMeaning uni fun2
         , Default (BuiltinSemanticsVariant fun1), Default (BuiltinSemanticsVariant fun2)
         ) => ToBuiltinMeaning uni (Either fun1 fun2) where

    type CostingPart uni (Either fun1 fun2) = (CostingPart uni fun1, CostingPart uni fun2)

    data BuiltinSemanticsVariant (Either fun1 fun2) =
        PairV (BuiltinSemanticsVariant fun1) (BuiltinSemanticsVariant fun2)
    toBuiltinMeaning (PairV semvarL _) (Left  fun) = case toBuiltinMeaning semvarL fun of
        BuiltinMeaning tySch toF denot ->
            BuiltinMeaning tySch toF (denot . fst)
    toBuiltinMeaning (PairV _ semvarR) (Right fun) = case toBuiltinMeaning semvarR fun of
        BuiltinMeaning tySch toF denot ->
            BuiltinMeaning tySch toF (denot . snd)

instance (Default (BuiltinSemanticsVariant fun1), Default (BuiltinSemanticsVariant fun2))
         => Default (BuiltinSemanticsVariant (Either fun1 fun2)) where
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
        , KnownKind kind, KnownTypeAst tyname uni a
        ) => KnownTypeAst tyname uni (MetaForall name a) where
    type IsBuiltin _ (MetaForall name a) = 'False
    type ToHoles _ (MetaForall name a) = '[TypeHole a]
    type ToBinds uni acc (MetaForall name a) = ToBinds uni (Insert ('GADT.Some name) acc) a
    toTypeAst _ = toTypeAst $ Proxy @a
instance MakeKnownIn DefaultUni term a => MakeKnownIn DefaultUni term (MetaForall name a) where
    makeKnown (MetaForall x) = makeKnown x
-- 'ReadKnownIn' doesn't make sense for 'MetaForall'.

data PlcListRep (a :: GHC.Type)
instance (tyname ~ TyName, KnownTypeAst tyname uni a) =>
        KnownTypeAst tyname uni (PlcListRep a) where
    type IsBuiltin _ (PlcListRep a) = 'False
    type ToHoles _ (PlcListRep a) = '[RepHole a]
    type ToBinds uni acc (PlcListRep a) = ToBinds uni acc a
    toTypeAst _ = TyApp () Plc.listTy . toTypeAst $ Proxy @a

instance tyname ~ TyName => KnownTypeAst tyname DefaultUni Void where
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

-- | For the most part we don't care about costing functions of example builtins, hence this class
-- for being explicit about not caring.
class Whatever a where
    -- | The costing function of a builtin whose costing function doesn't matter.
    whatever :: a

instance Whatever b => Whatever (a -> b) where
    whatever _ = whatever

instance Whatever ExBudgetStream where
    whatever = ExBudgetLast mempty

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

    data BuiltinSemanticsVariant ExtensionFun =
              ExtensionFunSemanticsVariant0
            | ExtensionFunSemanticsVariant1
        deriving stock (Enum, Bounded, Show)

    toBuiltinMeaning :: forall val. HasMeaningIn uni val
                     => BuiltinSemanticsVariant ExtensionFun
                     -> ExtensionFun
                     -> BuiltinMeaning val ()

    toBuiltinMeaning _semvar Factorial =
        makeBuiltinMeaning
            (\(n :: Integer) -> product [1..n])
            whatever

    toBuiltinMeaning _semvar ForallFortyTwo =
        makeBuiltinMeaning
            forallFortyTwo
            whatever
      where
        forallFortyTwo :: MetaForall ('TyNameRep @GHC.Type "a" 0) Integer
        forallFortyTwo = MetaForall 42

    toBuiltinMeaning _semvar SumInteger =
        makeBuiltinMeaning
            (sum :: [Integer] -> Integer)
            whatever

    toBuiltinMeaning _semvar Const =
        makeBuiltinMeaning
            const
            whatever

    toBuiltinMeaning _semvar Id =
        makeBuiltinMeaning
            Prelude.id
            whatever

    toBuiltinMeaning _semvar IdAssumeBool =
        makeBuiltinMeaning
            (Prelude.id :: Opaque val Bool -> Opaque val Bool)
            whatever

    toBuiltinMeaning _semvar IdAssumeCheckBool =
        makeBuiltinMeaning
            idAssumeCheckBoolPlc
            whatever
      where
        idAssumeCheckBoolPlc :: Opaque val Bool -> EvaluationResult Bool
        idAssumeCheckBoolPlc val =
            case asConstant val of
                Right (Some (ValueOf DefaultUniBool b)) -> EvaluationSuccess b
                _                                       -> EvaluationFailure

    toBuiltinMeaning _semvar IdSomeConstantBool =
        makeBuiltinMeaning
            idSomeConstantBoolPlc
            whatever
      where
        idSomeConstantBoolPlc :: SomeConstant uni Bool -> EvaluationResult Bool
        idSomeConstantBoolPlc = \case
            SomeConstant (Some (ValueOf DefaultUniBool b)) -> EvaluationSuccess b
            _                                              -> EvaluationFailure

    toBuiltinMeaning _semvar IdIntegerAsBool =
        makeBuiltinMeaning
            idIntegerAsBool
            whatever
      where
        idIntegerAsBool :: SomeConstant uni Integer -> EvaluationResult (SomeConstant uni Integer)
        idIntegerAsBool = \case
            con@(SomeConstant (Some (ValueOf DefaultUniBool _))) -> EvaluationSuccess con
            _                                                    -> EvaluationFailure

    toBuiltinMeaning _semvar IdFInteger =
        makeBuiltinMeaning
            (Prelude.id :: fi ~ Opaque val (f `TyAppRep` Integer) => fi -> fi)
            whatever

    toBuiltinMeaning _semvar IdList =
        makeBuiltinMeaning
            (Prelude.id :: la ~ Opaque val (PlcListRep a) => la -> la)
            whatever

    toBuiltinMeaning _semvar IdRank2 =
        makeBuiltinMeaning
            (Prelude.id
                :: afa ~ Opaque val (TyForallRep @GHC.Type a (TyVarRep f `TyAppRep` TyVarRep a))
                => afa -> afa)
            whatever

    toBuiltinMeaning _semvar ScottToMetaUnit =
        makeBuiltinMeaning
            ((\_ -> ())
                -- @(->)@ switches from the Rep context to the Type one. We could make @(->)@
                -- preserve the current context, but there's no such notion in the current
                -- elaboration machinery and we'd better not complicate it further just for the sake
                -- of tests looking a bit nicer. Instead we simply wrap the 'TyVarRep' with 'Opaque'
                -- (unlike in the case of @IdRank2@ where 'TyAppRep' preserves the Rep context).
                :: oa ~ Opaque val (TyVarRep a)
                => Opaque val (TyForallRep a (oa -> oa)) -> ())
            whatever

    toBuiltinMeaning _semvar FailingSucc =
        makeBuiltinMeaning
            @(Integer -> Integer)
            (\_ -> throw BuiltinErrorCall)
            whatever

    toBuiltinMeaning _semvar ExpensiveSucc =
        makeBuiltinMeaning
            @(Integer -> Integer)
            (\_ -> throw BuiltinErrorCall)
            (\_ _ -> ExBudgetLast $ unExRestrictingBudget enormousBudget)

    toBuiltinMeaning _semvar FailingPlus =
        makeBuiltinMeaning
            @(Integer -> Integer -> Integer)
            (\_ _ -> throw BuiltinErrorCall)
            whatever

    toBuiltinMeaning _semvar ExpensivePlus =
        makeBuiltinMeaning
            @(Integer -> Integer -> Integer)
            (\_ _ -> throw BuiltinErrorCall)
            (\_ _ _ -> ExBudgetLast $ unExRestrictingBudget enormousBudget)

    toBuiltinMeaning _semvar IsConstant =
        makeBuiltinMeaning
            isConstantPlc
            whatever
      where
        -- The type signature is just for clarity, it's not required.
        isConstantPlc :: Opaque val a -> Bool
        isConstantPlc = isRight . asConstant

    toBuiltinMeaning _semvar UnsafeCoerce =
        makeBuiltinMeaning
            unsafeCoercePlc
            whatever
      where
        -- The type signature is just for clarity, it's not required.
        unsafeCoercePlc :: Opaque val a -> Opaque val b
        unsafeCoercePlc = Opaque . unOpaque

    toBuiltinMeaning _semvar UnsafeCoerceEl =
        makeBuiltinMeaning
            unsafeCoerceElPlc
            whatever
      where
        unsafeCoerceElPlc
            :: SomeConstant DefaultUni [a]
            -> EvaluationResult (SomeConstant DefaultUni [b])
        unsafeCoerceElPlc (SomeConstant (Some (ValueOf uniList xs))) = do
            DefaultUniList _ <- pure uniList
            pure $ fromValueOf uniList xs

    toBuiltinMeaning _semvar Undefined =
        makeBuiltinMeaning
            undefined
            whatever

    toBuiltinMeaning _semvar Absurd =
        makeBuiltinMeaning
            absurd
            whatever

    toBuiltinMeaning _semvar ErrorPrime =
        makeBuiltinMeaning
            EvaluationFailure
            whatever

    toBuiltinMeaning _semvar Comma =
        makeBuiltinMeaning
            commaPlc
            whatever
      where
        commaPlc
            :: SomeConstant uni a
            -> SomeConstant uni b
            -> SomeConstant uni (a, b)
        commaPlc (SomeConstant (Some (ValueOf uniA x))) (SomeConstant (Some (ValueOf uniB y))) =
            fromValueOf (DefaultUniPair uniA uniB) (x, y)

    toBuiltinMeaning _semvar BiconstPair =
        makeBuiltinMeaning
            biconstPairPlc
            whatever
      where
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

    toBuiltinMeaning _semvar Swap =
        makeBuiltinMeaning
            swapPlc
            whatever
      where
        swapPlc
            :: SomeConstant uni (a, b)
            -> EvaluationResult (SomeConstant uni (b, a))
        swapPlc (SomeConstant (Some (ValueOf uniPairAB p))) = do
            DefaultUniPair uniA uniB <- pure uniPairAB
            pure $ fromValueOf (DefaultUniPair uniB uniA) (snd p, fst p)

    toBuiltinMeaning _semvar SwapEls =
        makeBuiltinMeaning
            swapElsPlc
            whatever
      where
        -- The type reads as @[(a, Bool)] -> [(Bool, a)]@.
        swapElsPlc
            :: SomeConstant uni [SomeConstant uni (a, Bool)]
            -> EvaluationResult (SomeConstant uni [SomeConstant uni (Bool, a)])
        swapElsPlc (SomeConstant (Some (ValueOf uniList xs))) = do
            DefaultUniList (DefaultUniPair uniA DefaultUniBool) <- pure uniList
            let uniList' = DefaultUniList $ DefaultUniPair DefaultUniBool uniA
            pure . fromValueOf uniList' $ map swap xs

    -- A dummy builtin to reflect the builtin-version of the 'ExtensionFun'.
    -- See Note [Builtin semantics variants]
    toBuiltinMeaning semvar ExtensionVersion =
        makeBuiltinMeaning
            @(() -> EvaluationResult Integer)
            (\(_ :: ()) -> EvaluationSuccess $ case semvar of
                    ExtensionFunSemanticsVariant0 -> 0
                    ExtensionFunSemanticsVariant1 -> 1)
            whatever

    -- We want to know if the CEK machine releases individual budgets after accounting for them and
    -- one way to ensure that is to check that individual budgets are GCed in chunks rather than all
    -- at once when evaluation of the builtin finishes. This builtin returns a list of the maximum
    -- numbers of individual budgets retained between GC calls. If the returned list is long (for
    -- some definition of "long", see the tests), then chances are individual budgets are not
    -- retained unnecessarily, and if it's too short (again, see the tests), then they are.
    --
    -- We track how many budgets get GCed by attaching a finalizer (see "System.Mem.Weak") to each
    -- of them.
    toBuiltinMeaning _ TrackCosts = unsafePerformIO $ do
        -- A variable for storing the number of elements from the stream of budgets pending GC.
        pendingGcVar <- newMVar 0
        -- A variable for storing all the final numbers from @pendingGcVar@ appearing there right
        -- before another GC is triggered. We store the results in reverse order for fast consing
        -- and then 'reverse' them in the denotation of the builtin.
        numsOfGcedVar <- newMVar []
        let -- A function to run when GC picks up an individual budget.
            finalize =
                tryTakeMVar pendingGcVar >>= \case
                    -- If @pendingGcVar@ happens to be empty, we say that no budgets were released
                    -- and don't update @pendingGcVar@. I.e. this entire testing machinery can
                    -- affect how budgets are retained, but the impact of the 'MVar' business is
                    -- negligible, since @pendingGcVar@ is filled immediately after it's emptied.
                    Nothing -> pure ()
                    -- If @pendingGcVar@ is not empty, then we cons its content to the resulting
                    -- list and put @0@ as the new content of the variable.
                    Just pendingGc -> do
                        _ <- modifyMVar_ numsOfGcedVar $ pure . (pendingGc :)
                        putMVar pendingGcVar 0

            -- Register an element of the stream of budgets by incrementing the counter storing the
            -- number of elements pending GC and attaching the @finalize@ finalizer to the element.
            regBudget budget = do
                pendingGc <- takeMVar pendingGcVar
                let pendingGc' = succ pendingGc
                putMVar pendingGcVar pendingGc'
                addFinalizer budget finalize
                -- We need to trigger GC occasionally (otherwise it can easily take more than 100k
                -- elements before GC is triggered and the number can go much higher depending on
                -- the RTS options), so we picked 100 elements as a cutoff number. Doing GC less
                -- often makes tests slower, doing GC more often requires us to generate longer
                -- streams in tests in order to observe meaningful results making tests slower.
                when (pendingGc' >= 100) performMinorGC

            -- Call @regBudget@ over each element of the stream of budgets.
            regBudgets (ExBudgetLast budget) = do
                regBudget budget
                -- Run @finalize@ one final time before returning the last budget.
                finalize
                -- Make all outstanding finalizers inert, so that we don't mix up budgets GCed
                -- during spending with budgets GCed right after spending finishes.
                _ <- takeMVar pendingGcVar
                pure $ ExBudgetLast budget
            regBudgets (ExBudgetCons budget budgets) = do
                regBudget budget
                -- Without 'unsafeInterleaveIO' this function would traverse the entire stream
                -- before returning anything, which isn't what costing functions normally do and so
                -- we don't want to have such behavior in a test.
                budgets' <- unsafeInterleaveIO $ regBudgets budgets
                pure $ ExBudgetCons budget budgets'

            -- Just a random model that keeps the costs coming from the 'ExMemoryUsage' instance.
            linear1 = ModelOneArgumentLinearCost $ OneVariableLinearFunction 1 1
            model   = CostingFun linear1 linear1
        pure $ makeBuiltinMeaning
            @(Data -> [Integer])
            (\_ -> unsafePerformIO $ reverse <$> readMVar numsOfGcedVar)
            (\_ -> unsafePerformIO . regBudgets . runCostingFunOneArgument model)

instance Default (BuiltinSemanticsVariant ExtensionFun) where
    def = ExtensionFunSemanticsVariant1
