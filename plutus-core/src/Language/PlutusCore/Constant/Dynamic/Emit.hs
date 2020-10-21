{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeOperators     #-}

module Language.PlutusCore.Constant.Dynamic.Emit
    ( withEmit
    ) where

import           Data.IORef
import           System.IO.Unsafe

-- | Feed the provided continuation with a function tracing a value to the outside of the
-- continuation where traced values get collected in a list.
--
-- If the tracing function is used in pure code via 'unsafePerformIO' and a @b@ returned by the
-- continuation is not forced inside the continuation, then no traced values will be collected as
-- no computation will occur. It is however not too late to force the resulting @b@ outside of the
-- continuation and reference the list of traced value afterwards. We don't attempt to force
-- anything ourselves, because the caller may want to force the resulting @b@ to WHNF or to NF or
-- not to force at all and just not trace anything if the result of the continuation is not used.
--
-- This function does not stream values lazily. There is a version that allows for lazy streaming,
-- but we do not have it here because it's way too convoluted.
-- See https://github.com/input-output-hk/plutus/pull/336 if you need lazy streaming.
withEmit :: ((a -> IO ()) -> IO b) -> IO ([a], b)
withEmit k = do
    xsVar <- newIORef id
    -- 'atomicModifyIORef' is to make tracing thread-safe. We don't bother using the strict version,
    -- since values get collected in a difference list (i.e. a function) anyway.
    y <- k $ \x -> atomicModifyIORef xsVar $ \ds -> (ds . (x :), ())
    -- We need the 'unsafeInterleaveIO' in order to support this: "It is however not too late to
    -- force the resulting @b@ outside of the continuation and reference the list of traced value
    -- afterwards".
    ds <- unsafeInterleaveIO $ readIORef xsVar
    return (ds [], y)
