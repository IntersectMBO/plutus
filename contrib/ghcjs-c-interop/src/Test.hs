{-# language ForeignFunctionInterface #-}
module Test where

import Foreign

foreign import ccall "wrapper" createAddPtr :: (Int -> Int -> Int) -> IO (FunPtr (Int -> Int -> Int))
foreign import ccall "test_fold" test_fold :: (FunPtr (Int -> Int -> Int)) -> Int -> Int

foreign import ccall "wrapper" createAddPtrIO :: (Int -> Int -> IO Int) -> IO (FunPtr (Int -> Int -> IO Int))
foreign import ccall "test_fold" test_foldIO :: (FunPtr (Int -> Int -> IO Int)) -> Int -> IO Int

add :: Int -> Int -> Int
add x y = x + y
{-# NOINLINE add #-}

addIO :: Int -> Int -> IO Int
addIO x y = do
    -- print $ (show x) ++ " + " ++ (show y) ++ " = " ++ (show $ x + y)
    return $ x+y
{-# NOINLINE addIO #-}

doFold :: IO ()
doFold = do
    addPtr <- createAddPtr add
    addPtrIO <- createAddPtrIO addIO
    -- you can use addPtr like any other FunPtr (e.g. give it to foreign code)
    print $ foldl (+) 0 [(0::Int)..10]
    print $ test_fold addPtr 10
    print =<< test_foldIO addPtrIO 10
    -- you MUST free the FunPtr, otherwise it won't be collected
    -- freeHaskellFunPtr addPtrIO
    freeHaskellFunPtr addPtr