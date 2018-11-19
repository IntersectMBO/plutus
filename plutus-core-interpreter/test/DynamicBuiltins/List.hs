-- | A dynamic built-in type test.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module DynamicBuiltins.List where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.StdLib.Data.List
import           Language.PlutusCore.StdLib.Data.Unit
import           Language.PlutusCore.StdLib.Meta

import           Language.PlutusCore.Interpreter.CekMachine

import           DynamicBuiltins.Call

import           Control.Exception                          (evaluate)
import           Control.Monad                              (replicateM)
import           Control.Monad.IO.Class                     (liftIO)
import           Data.Char
import           Data.Functor.Compose                       (Compose (..))
import           Data.IORef
import           Data.Proxy
import           Data.Traversable                           (for)
import           Hedgehog                                   hiding (Size)
import qualified Hedgehog.Gen                               as Gen
import qualified Hedgehog.Range                             as Range
import           System.IO.Unsafe
import           Test.Tasty
import           Test.Tasty.Hedgehog

import           DynamicBuiltins.Char

-- > /\(a :: *) (r :: *) -> \(f : r -> a -> r) ->
-- >     fix {r} {list a -> r} \(rec : r -> list a -> r) (z : r) (xs : list a) ->
-- >         unwrap xs {r} z \(x : a) (xs' : list a) -> rec (f z x) xs'

-- [dyn] -> Quote (Term TyName Name ())
-- getListToBuiltinList :: Type TyName () -> [Term TyName Name ()] -> Quote (Term TyName Name ())

argumentProxy :: proxy (f a) -> Proxy a
argumentProxy _ = Proxy

-- let collectChar = dynamicCallAssign TypedBuiltinDyn $ \c -> modifyIORef' charsVar (c :)
--     env         = insertDynamicBuiltinNameDefinition collectChar mempty
--     term        = Apply () dynamicCall . runQuote $ unsafeMakeDynamicBuiltin char

-- emit : a -> unit

-- dyn = dynamicBuiltinTypeAsType _
-- foldList {dyn} {()} (\(r : unit) -> emit) unitval

withResultProxy :: (Proxy dyn -> result dyn) -> result dyn
withResultProxy k = k Proxy

instance KnownDynamicBuiltinType dyn => KnownDynamicBuiltinType [dyn] where
    dynamicBuiltinType proxyListDyn = DynamicBuiltinType $ "[" <> dynName <> "]" where
        DynamicBuiltinType dynName = dynamicBuiltinType $ argumentProxy proxyListDyn

    makeDynamicBuiltin xs = do
        mayDyns <- getCompose $ traverse (Compose . makeDynamicBuiltin) xs
        let argTy = dynamicBuiltinTypeAsType xs  -- Here we use '[]' as a @proxy@.
                                                 -- Don't judge me, I'm only human.
        traverse (getListToBuiltinList argTy) mayDyns

    readDynamicBuiltin list = withResultProxy $ \proxyListDyn -> do
        let (xs, res) = unsafePerformIO . withEmitEvaluateCek TypedBuiltinDyn $ \emit ->
                runQuote $ do
                    let dyn = dynamicBuiltinTypeAsType $ argumentProxy proxyListDyn
                    unit     <- getBuiltinUnit
                    unitval  <- getBuiltinUnitval
                    foldList <- getBuiltinFoldList
                    u <- freshName () "u"
                    return
                        $ mkIterApp () (mkIterInst () foldList [dyn, unit])
                            [ LamAbs () u unit emit
                            , unitval
                            , list
                            ]
        _ <- evaluationResultToMaybe res
        Just xs

blah :: Maybe String
blah = runQuote (makeDynamicBuiltin ("abc" :: String)) >>= readDynamicBuiltin

instance PrettyDynamic a => PrettyDynamic [a] where
    prettyDynamic = undefined

-- -- | Generate a bunch of 'Char's, put each of them into a 'Term', apply a dynamic built-in name over
-- -- each of these terms such that being evaluated it calls a Haskell function that prepends a char to
-- -- the contents of an external 'IORef'. In the end read the 'IORef', reverse its contents and check
-- -- that you got the exact same sequence of 'Char's that was originally generated.
-- -- Calls 'unsafePerformIO' internally while evaluating the term, because the CEK machine can only handle
-- -- pure things and 'unsafePerformIO' is the way to pretend an effecful thing is pure.
-- test_onEach :: TestTree
-- test_onEach = testProperty "collect chars" . property $ do
--     len <- forAll . Gen.integral $ Range.linear 0 20
--     charsVar <- liftIO $ newIORef []
--     chars <- replicateM len $ do
--         char <- forAll Gen.unicode
--         let onEach = dynamicOnEachAssign TypedBuiltinDyn $ \c -> modifyIORef' charsVar (c :)
--             env    = insertDynamicBuiltinNameDefinition onEach mempty
--             term   = Apply () dynamicOnEach $ unsafeMakeDynamicBuiltin char
--         _ <- liftIO . evaluate $ evaluateCek env term
--         return char
--     chars' <- liftIO $ reverse <$> readIORef charsVar
--     chars === chars'
