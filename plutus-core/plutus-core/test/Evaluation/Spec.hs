{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Evaluation.Spec where

import Control.Exception
import Control.Monad.Except
import Control.Monad.Extra
import Data.ByteString qualified as BS
import Data.Functor (($>))
import Data.Int (Int64)
import Data.Kind qualified as GHC
import Data.List.Extra qualified as List
import Data.Text (Text)
import Data.Type.Equality
import Data.Typeable (splitTyConApp)
import Evaluation.Machines (test_machines)
import Hedgehog hiding (Opaque, Var, eval)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Internal.Property (failWith)
import Hedgehog.Range qualified as Range
import PlutusCore hiding (Term)
import PlutusCore qualified as PLC
import PlutusCore.Builtin
import PlutusCore.Data (Data (..))
import PlutusCore.Generators (forAllNoShow)
import PlutusCore.Generators.AST
import PlutusCore.Pretty
import Test.Tasty
import Test.Tasty.Hedgehog
import Type.Reflection
import Unsafe.Coerce

type Term = PLC.Term TyName Name DefaultUni DefaultFun ()

test_builtinsDon'tThrow :: TestTree
test_builtinsDon'tThrow =
    testGroup
        "Builtins don't throw"
        $ fmap (\fun -> testProperty (display fun) $ prop_builtinsDon'tThrow fun) List.enumerate

prop_builtinsDon'tThrow :: DefaultFun -> Property
prop_builtinsDon'tThrow bn = property $ do
    args <- forAllNoShow . Gen.choice $ [genArgsWellTyped bn, genArgsArbitrary bn]
    mbErr <-
        liftIO $
            catch
                (($> Nothing) . evaluate . runEmitter . runExceptT $ eval args)
                (pure . pure)
    whenJust mbErr $ \(e :: SomeException) -> do
        let msg =
                "Builtin function evaluation failed"
                    <> "Function: "
                    <> display bn
                    <> "Arguments: "
                    <> display args
                    <> "Error: "
                    <> show e
        failWith Nothing msg
  where
    meaning :: BuiltinMeaning Term (CostingPart DefaultUni DefaultFun)
    meaning = toBuiltinMeaning bn

    eval :: [Term] -> MakeKnownM Term
    eval args0 = case meaning of
        BuiltinMeaning _ _ runtime -> go (_broRuntimeScheme runtime) (_broImmediateF runtime) args0
      where
        go ::
            forall n.
            RuntimeScheme n ->
            ToRuntimeDenotationType Term n ->
            [Term] ->
            MakeKnownM Term
        go sch f args = case (sch, args) of
            (RuntimeSchemeArrow sch', a : as) -> do
                res <- liftEither (f a)
                go sch' res as
            (RuntimeSchemeResult, []) -> f
            (RuntimeSchemeAll sch', _) -> go sch' f args
            _ -> error $ "Wrong number of args for builtin " <> display bn <> ": " <> display args0

{- | Generate well-typed Term arguments to a builtin function.
 TODO: currently it only generates constant terms.
-}
genArgsWellTyped :: DefaultFun -> Gen [Term]
genArgsWellTyped = genArgs (fmap (Constant ()) . genValArg)

-- | Generate arbitrary (most likely ill-typed) Term arguments to a builtin function.
genArgsArbitrary :: DefaultFun -> Gen [Term]
genArgsArbitrary = genArgs (const (runAstGen genTerm))

-- | Generate value arguments to a builtin function based on its `TypeScheme`.
genArgs :: (forall k (a :: k). TypeRep a -> Gen Term) -> DefaultFun -> Gen [Term]
genArgs genArg bn = sequenceA $ case meaning of
    BuiltinMeaning tySch _ _ -> go tySch
      where
        go :: forall args res. TypeScheme Term args res -> [Gen Term]
        go = \case
            TypeSchemeResult    -> []
            TypeSchemeArrow sch -> genArg (typeRep @(Head args)) : go sch
            TypeSchemeAll _ sch -> go sch
  where
    meaning :: BuiltinMeaning Term (CostingPart DefaultUni DefaultFun)
    meaning = toBuiltinMeaning bn

-- | Generate one value argument to a builtin function based on its `TypeRep`.
genValArg :: forall k (a :: k). TypeRep a -> Gen (Some (ValueOf DefaultUni))
genValArg tr
    | Just HRefl <- eqTypeRep tr (typeRep @()) = pure $ someValue ()
    | Just HRefl <- eqTypeRep tr (typeRep @Integer) = someValue <$> genInteger
    | Just HRefl <- eqTypeRep tr (typeRep @Int) = someValue <$> genInteger
    | Just HRefl <- eqTypeRep tr (typeRep @Bool) = someValue <$> Gen.bool
    | Just HRefl <- eqTypeRep tr (typeRep @BS.ByteString) = someValue <$> genByteString
    | Just HRefl <- eqTypeRep tr (typeRep @Text) = someValue <$> genText
    | Just HRefl <- eqTypeRep tr (typeRep @Data) = someValue <$> genData 5
    | Just [SomeTypeRep tr1, SomeTypeRep tr2] <- matchTyCon @(,) tr = do
        Some (ValueOf uni1 val1) <- genValArg tr1
        Some (ValueOf uni2 val2) <- genValArg tr2
        pure
            ( someValueOf
                (DefaultUniApply (DefaultUniApply DefaultUniProtoPair uni1) uni2)
                (val1, val2)
            )
    | Just [SomeTypeRep trElem] <- matchTyCon @[] tr = do
        Some (ValueOf uniElem (_ :: b)) <- genValArg trElem
        args <- Gen.list (Range.linear 0 10) $ genValArg trElem
        let valElems :: [b]
            valElems = (\(Some (ValueOf _ valElem')) -> unsafeCoerce valElem') <$> args
        pure (someValueOf (DefaultUniApply DefaultUniProtoList uniElem) valElems)
    -- Descend upon `Opaque`
    | Just [_, SomeTypeRep tr'] <- matchTyCon @Opaque tr = genValArg tr'
    -- Descend upon `SomeConstant`
    | Just [_, SomeTypeRep tr'] <- matchTyCon @SomeConstant tr = genValArg tr'
    -- In the current implementation, all type variables are instantiated
    -- to `Integer` (TODO: change this).
    | Just _ <- matchTyCon @(TyVarRep @GHC.Type) tr =
        someValue <$> genInteger
    | otherwise =
        error $
            "genValArg: I don't know how to generate builtin arguments of this type: " <> show tr

-- | If the given `TypeRep`'s `TyCon` is @con@, return its type arguments.
matchTyCon :: forall con a. (Typeable con) => TypeRep a -> Maybe [SomeTypeRep]
matchTyCon tr = if con == con' then Just args else Nothing
  where
    (con, args) = splitTyConApp (SomeTypeRep tr)
    con' = typeRepTyCon (typeRep @con)

-- | If the given `TypeRep`'s `TyCon` matches the given module and name, return its type arguments.
matchTyCon' :: forall a. String -> String -> TypeRep a -> Maybe [SomeTypeRep]
matchTyCon' modu name tr = if modu == modu' && name == name' then Just args else Nothing
  where
    (con, args) = splitTyConApp (SomeTypeRep tr)
    modu' = tyConModule con
    name' = tyConName con

type family Head a where
    Head (x ': xs) = x

----------------------------------------------------------
-- Generators

genInteger :: Gen Integer
genInteger = fromIntegral @Int64 <$> Gen.enumBounded

genByteString :: Gen BS.ByteString
genByteString = Gen.utf8 (Range.linear 0 100) Gen.enumBounded

genText :: Gen Text
genText = Gen.text (Range.linear 0 100) Gen.enumBounded

genData :: Int -> Gen Data
genData depth =
    Gen.choice $
        [genI, genB]
            <> [ genRec | depth > 1, genRec <-
                                        [ genList (depth - 1)
                                        , genMap (depth - 1)
                                        , genConstr (depth - 1)
                                        ]
               ]

genI :: Gen Data
genI = I <$> genInteger

genB :: Gen Data
genB = B <$> genByteString

genList :: Int -> Gen Data
genList depth = List <$> Gen.list (Range.linear 0 5) (genData (depth - 1))

genMap :: Int -> Gen Data
genMap depth =
    Map
        <$> Gen.list
            (Range.linear 0 5)
            ((,) <$> genData (depth - 1) <*> genData (depth - 1))

genConstr :: Int -> Gen Data
genConstr depth =
    Constr <$> genInteger
        <*> Gen.list
            (Range.linear 0 5)
            (genData (depth - 1))

test_evaluation :: TestTree
test_evaluation =
    testGroup
        "evaluation"
        [ test_machines
        , test_builtinsDon'tThrow
        ]
