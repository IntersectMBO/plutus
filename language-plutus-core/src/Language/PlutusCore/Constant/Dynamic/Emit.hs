{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module Language.PlutusCore.Constant.Dynamic.Emit
    ( withEmit
    , withLazyEmit
    , withEmitEvaluateBy
    ) where

import           Language.PlutusCore.Constant.Dynamic.Call
import           Language.PlutusCore.Constant.Function
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Type

import           Control.Exception                         (evaluate)
import           Data.IORef
import           Data.Functor                              (void)
import           Control.Concurrent.MVar
import           Control.Concurrent
import           System.IO.Unsafe                          (unsafePerformIO, unsafeInterleaveIO)

withEmit :: ((a -> IO ()) -> IO b) -> IO ([a], b)
withEmit k = do
    xsVar <- newIORef id
    -- We may want to place 'unsafeInterleaveIO' here just to be lazy and cool.
    y <- k $ \x -> modifyIORef xsVar $ \ds -> ds . (x :)
    ds <- readIORef xsVar
    return (ds [], y)

-- | Take 'Just's from an 'MVar' until a 'Nothing' pops up and
-- collect values 'Just's store into a list.
readLazyListMVar :: MVar (Maybe a) -> IO [a]
readLazyListMVar mayXVar = go where
    go = unsafeInterleaveIO $ do
        mayX <- takeMVar mayXVar
        case mayX of
            Nothing -> return []
            Just x  -> (x :) <$> go

-- | Same as 'withEmit', but streams emitted elements to the outside lazily.
-- Unsafe w.r.t. async exceptions (Ctrl-c does not kill the spawned threads).
withLazyEmit :: ((a -> IO ()) -> IO b) -> IO ([a], b)
withLazyEmit k = do
    -- A variable to store emitted elements in.
    mayXVar <- newEmptyMVar
    -- A variable to store the result of the main computation.
    resVar <- newEmptyMVar
    void . forkIO $ do
        -- The main computation. Put each emitted element in an 'MVar'.
        y <- k $ putMVar mayXVar . Just
        -- Signal that elements are over in order to let 'readLazyListMVar' finish.
        putMVar mayXVar Nothing
        -- Record the result of the computation.
        putMVar resVar y
    -- Read emitted elements lazily.
    xs <- readLazyListMVar mayXVar
    -- Force the list in a separate thread in order to call @takeMVar mayXVar@
    -- in order to ublock @putMVar mayXVar@. This should also perhaps be GC-friendly.
    void . forkIO . void . evaluate $ length xs
    -- Lazily read the result of the main computation.
    -- Docs of 'fixIO' suggest to use @unsafeDupableInterleaveIO . readMVar@ here, but whatever.
    y <- unsafeInterleaveIO $ takeMVar resVar
    return (xs, y)

globalUniqueVar :: IORef Int
globalUniqueVar = unsafePerformIO $ newIORef 0
{-# NOINLINE globalUniqueVar #-}

nextGlobalUnique :: IO Int
nextGlobalUnique = atomicModifyIORef' globalUniqueVar $ \i -> (i, succ i)

-- We do not type check terms here, because type checking of nested dynamic built-in types simply
-- does not work. The type checker can't be quickly repaired, so we keep it like this for now.
withEmitEvaluateBy
    :: Evaluator Term m
    -> (forall size. TypedBuiltin size a)
    -> (Term TyName Name () -> Term TyName Name ())
    -> IO ([a], m EvaluationResult)
withEmitEvaluateBy eval tb toTerm =
    withEmit $ \emit -> do
        counter <- nextGlobalUnique
        let dynamicEmitName       = DynamicBuiltinName $ "emit" <> prettyText counter
            dynamicEmitTerm       = dynamicCall dynamicEmitName
            dynamicEmitDefinition = dynamicCallAssign tb dynamicEmitName emit
            env  = insertDynamicBuiltinNameDefinition dynamicEmitDefinition mempty
            term = toTerm dynamicEmitTerm
        evaluate $ eval env term
