-- | A dynamic built-in type test.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}

module DynamicBuiltins.Char (test_onChar) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant

import           Language.PlutusCore.Interpreter.CekMachine

import           Control.Exception                          (evaluate)
import           Control.Monad                              (replicateM)
import           Control.Monad.IO.Class                     (liftIO)
import           Data.Char
import           Data.IORef
import           Data.Maybe                                 (fromMaybe)
import           Hedgehog
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

dynamicOnCharName :: DynamicBuiltinName
dynamicOnCharName = DynamicBuiltinName "onChar"

dynamicOnCharAssign :: (Char -> IO ()) -> DynamicBuiltinNameDefinition
dynamicOnCharAssign f =
    DynamicBuiltinNameDefinition dynamicOnCharName $ DynamicBuiltinNameMeaning sch sem where
        sch :: TypeScheme size (Char -> ()) ()
        sch =
            TypeSchemeBuiltin TypedBuiltinDyn `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeValue 1) TypedBuiltinSizedSize)  -- Hacky-hacky.
        sem = unsafePerformIO . f

dynamicOnChar :: Term tyname name ()
dynamicOnChar = dynamicBuiltinNameAsTerm dynamicOnCharName

charToTerm :: Char -> Term TyName Name ()
charToTerm = fromMaybe (error "charToTerm: failed") . makeDynamicBuiltin

-- | Generate a bunch of 'Char's, put each of them into a 'Term', apply a dynamic built-in name over
-- each of these terms such that being evaluated it calls a Haskell function that prepends a char to
-- the contents of an external 'IORef'. In the end read the 'IORef', reverse its contents and check
-- that you got the exact same sequence of 'Char's that was originally generated.
-- Calls 'unsafePerformIO' internally while evaluating the term, because the CEK machine can only handle
-- pure things and 'unsafePerformIO' is the way to pretend an effecful thing is pure.
test_onChar :: TestTree
test_onChar = testProperty "collect chars" . property $ do
    len <- forAll . Gen.integral $ Range.linear 0 20
    charsVar <- liftIO $ newIORef []
    chars <- replicateM len $ do
        char <- forAll Gen.unicode
        let onChar = dynamicOnCharAssign $ \c -> modifyIORef' charsVar (c :)
            env    = insertDynamicBuiltinNameDefinition onChar mempty
            term   = Apply () dynamicOnChar $ charToTerm char
        _ <- liftIO . evaluate $ evaluateCek env term
        return char
    chars' <- liftIO $ reverse <$> readIORef charsVar
    chars === chars'
