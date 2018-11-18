-- | A dynamic built-in type test.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module DynamicBuiltins.Char (test_onEach) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant

import           Language.PlutusCore.Interpreter.CekMachine

import           Control.Exception                          (evaluate)
import           Control.Monad                              (replicateM)
import           Control.Monad.IO.Class                     (liftIO)
import           Data.Char
import           Data.IORef
import           Hedgehog                                   hiding (Size)
import qualified Hedgehog.Gen                               as Gen
import qualified Hedgehog.Range                             as Range
import           System.IO.Unsafe
import           Test.Tasty
import           Test.Tasty.Hedgehog

-- Encode 'Char' from Haskell as @integer 4@ from PLC.
instance KnownDynamicBuiltinType Char where
    dynamicBuiltinType _ = DynamicBuiltinType "char"

    makeDynamicBuiltin = fmap (Constant ()) . makeBuiltinInt 4 . fromIntegral . ord

    readDynamicBuiltin (Constant () (BuiltinInt () 4 int)) = Just . chr $ fromIntegral int
    readDynamicBuiltin _                                   = Nothing

instance PrettyDynamic Char

dynamicOnEachName :: DynamicBuiltinName
dynamicOnEachName = DynamicBuiltinName "onEach"

dynamicOnEachAssign
    :: (forall size. TypedBuiltin size a) -> (a -> IO ()) -> DynamicBuiltinNameDefinition
dynamicOnEachAssign tb f =
    DynamicBuiltinNameDefinition dynamicOnEachName $ DynamicBuiltinNameMeaning sch sem where
        sch =
            TypeSchemeBuiltin tb `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeValue 1) TypedBuiltinSizedSize)  -- Hacky-hacky.
        sem = unsafePerformIO . f

dynamicOnEach :: Term tyname name ()
dynamicOnEach = dynamicBuiltinNameAsTerm dynamicOnEachName

-- | Generate a bunch of 'Char's, put each of them into a 'Term', apply a dynamic built-in name over
-- each of these terms such that being evaluated it calls a Haskell function that prepends a char to
-- the contents of an external 'IORef'. In the end read the 'IORef', reverse its contents and check
-- that you got the exact same sequence of 'Char's that was originally generated.
-- Calls 'unsafePerformIO' internally while evaluating the term, because the CEK machine can only handle
-- pure things and 'unsafePerformIO' is the way to pretend an effecful thing is pure.
test_onEach :: TestTree
test_onEach = testProperty "collect chars" . property $ do
    len <- forAll . Gen.integral $ Range.linear 0 20
    charsVar <- liftIO $ newIORef []
    chars <- replicateM len $ do
        char <- forAll Gen.unicode
        let onEach = dynamicOnEachAssign TypedBuiltinDyn $ \c -> modifyIORef' charsVar (c :)
            env    = insertDynamicBuiltinNameDefinition onEach mempty
            term   = Apply () dynamicOnEach $ unsafeMakeDynamicBuiltin char
        _ <- liftIO . evaluate $ evaluateCek env term
        return char
    chars' <- liftIO $ reverse <$> readIORef charsVar
    chars === chars'
