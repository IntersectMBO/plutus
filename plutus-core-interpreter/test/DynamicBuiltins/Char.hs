-- | A dynamic built-in type test.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module DynamicBuiltins.Char
    ( test_collectChars
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.StdLib.Data.Unit

import           DynamicBuiltins.Call

import           Control.Monad.IO.Class               (liftIO)
import           Data.Char
import           Data.Proxy
import           Hedgehog                             hiding (Size, Var)
import qualified Hedgehog.Gen                         as Gen
import qualified Hedgehog.Range                       as Range
import           Test.Tasty
import           Test.Tasty.Hedgehog

-- Encode 'Char' from Haskell as @integer 4@ from PLC.
instance KnownDynamicBuiltinType Char where
    dynamicBuiltinType _ = DynamicBuiltinType "char"

    makeDynamicBuiltin = pure . fmap (Constant ()) . makeBuiltinInt 4 . fromIntegral . ord

    readDynamicBuiltin (Constant () (BuiltinInt () 4 int)) = Just . chr $ fromIntegral int
    readDynamicBuiltin _                                   = Nothing

builtinChar :: Type tyname ()
builtinChar = dynamicBuiltinTypeAsType (Proxy :: Proxy Char)

instance PrettyDynamic Char

-- | Generate a bunch of 'Char's, put each of them into a 'Term', apply a dynamic built-in name over
-- each of these terms such that being evaluated it calls a Haskell function that appends a char to
-- the contents of an external 'IORef' and assemble all the resulting terms together into a single term
-- where all characters are passed to lambdas and ignored, so that only 'unitval' is returned in the end.
-- After evaluation of the CEK machine finished, read the 'IORef' and check that you got the exact same
-- sequence of 'Char's that was originally generated.
-- Calls 'unsafePerformIO' internally while evaluating the term, because the CEK machine can only handle
-- pure things and 'unsafePerformIO' is the way to pretend an effecful thing is pure.
test_collectChars :: TestTree
test_collectChars = testProperty "collectChars" . property $ do
    str <- forAll $ Gen.string (Range.linear 0 20) Gen.unicode
    (str', _) <- liftIO . withEmitEvaluateCek TypedBuiltinDyn $ \emit ->
        runQuote $ rename =<< do
            chars <- traverse unsafeMakeDynamicBuiltin str
            unit    <- getBuiltinUnit
            unitval <- getBuiltinUnitval
            ignore <- do
                x <- freshName () "x"
                y <- freshName () "y"
                return
                    . LamAbs () x builtinChar
                    . LamAbs () y unit
                    $ Var () y
            let step arg rest = mkIterApp () ignore [Apply () emit arg, rest]
            return $ foldr step unitval chars
    str === str'
