-- Module      : Foundation.Conduit.Internal
-- License     : BSD-style
-- Maintainer  : Foundation
-- Stability   : experimental
-- Portability : portable
--
-- Taken from the conduit package almost verbatim, and
-- Copyright (c) 2012 Michael Snoyman
--
{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-inline-rule-shadowing #-}

module Foundation.Conduit.Internal
    ( Pipe(..)
    , Conduit(..)
    , ZipSink(..)
    , ResourceT(..)
    , MonadResource(..)
    , runResourceT
    , await
    , awaitForever
    , yield
    , yieldOr
    , leftover
    , runConduit
    , runConduitRes
    , runConduitPure
    , fuse
    , bracketConduit
    ) where

import Basement.Imports hiding (throw)
import Foundation.Monad
import Foundation.Numerical
import Basement.Monad
import Control.Monad ((>=>), liftM, void, mapM_, join)
import Control.Exception (SomeException, mask_)
import Data.IORef (atomicModifyIORef)

-- | A pipe producing and consuming values
--
-- A basic intuition is that every @Pipe@ produces a stream of /output/ values
-- and eventually indicates that this stream is terminated by sending a
-- /result/. On the receiving end of a @Pipe@, these become the /input/ and /upstream/
-- parameters.
data Pipe leftOver input output upstream monad result =
      -- | Provide new output to be sent downstream. This constructor has three
      -- fields: the next @Pipe@ to be used, a finalization function, and the
      -- output value.
      Yield (Pipe leftOver input output upstream monad result) (monad ()) output
      -- | Request more input from upstream. The first field takes a new input
      -- value and provides a new @Pipe@. The second takes an upstream result
      -- value, which indicates that upstream is producing no more results.
    | Await (input -> Pipe leftOver input output upstream monad result)
                (upstream -> Pipe leftOver input output upstream monad result)
      -- | Processing with this @Pipe@ is complete, providing the final result.
    | Done result
      -- | Require running of a monadic action to get the next @Pipe@.
    | PipeM (monad (Pipe leftOver input output upstream monad result))
      -- | Return leftover input, which should be provided to future operations.
    | Leftover (Pipe leftOver input output upstream monad result) leftOver

instance Applicative m => Functor (Pipe l i o u m) where
    fmap = (<$>)
    {-# INLINE fmap #-}

instance Applicative m => Applicative (Pipe l i o u m) where
    pure = Done
    {-# INLINE pure #-}

    Yield p c o  <*> fa = Yield (p <*> fa) c o
    Await p c    <*> fa = Await (\i -> p i <*> fa) (\o -> c o <*> fa)
    Done r       <*> fa = r <$> fa
    PipeM mp     <*> fa = PipeM ((<*> fa) <$> mp)
    Leftover p i <*> fa = Leftover (p <*> fa) i
    {-# INLINE (<*>) #-}

instance (Functor m, Monad m) => Monad (Pipe l i o u m) where
    return = Done
    {-# INLINE return #-}

    Yield p c o  >>= fp = Yield    (p >>= fp)            c          o
    Await p c    >>= fp = Await    (p >=> fp)            (c >=> fp)
    Done x       >>= fp = fp x
    PipeM mp     >>= fp = PipeM    ((>>= fp) <$> mp)
    Leftover p i >>= fp = Leftover (p >>= fp)            i

-- | A component of a conduit pipeline, which takes a stream of
-- @input@, produces a stream of @output@, performs actions in the
-- underlying @monad@, and produces a value of @result@ when no more
-- output data is available.
newtype Conduit input output monad result = Conduit
    { unConduit :: forall a .  (result -> Pipe input input output () monad a) -> Pipe input input output () monad a
    }

instance Functor (Conduit i o m) where
    fmap f (Conduit c) = Conduit $ \resPipe -> c (resPipe . f)

instance Applicative (Conduit i o m) where
    pure x = Conduit ($ x)
    {-# INLINE pure #-}

    fab <*> fa = fab >>= \ab -> fa >>= \a -> pure (ab a)
    {-# INLINE (<*>) #-}

instance Monad (Conduit i o m) where
    return = pure
    Conduit f >>= g = Conduit $ \h -> f $ \a -> unConduit (g a) h

instance MonadTrans (Conduit i o) where
    lift m = Conduit $ \rest -> PipeM $ liftM rest m

instance MonadIO m => MonadIO (Conduit i o m) where
    liftIO = lift . liftIO

instance MonadFailure m => MonadFailure (Conduit i o m) where
    type Failure (Conduit i o m) = Failure m
    mFail = lift . mFail

instance MonadThrow m => MonadThrow (Conduit i o m) where
    throw = lift . throw

instance MonadCatch m => MonadCatch (Conduit i o m) where
    catch (Conduit c0) onExc = Conduit $ \rest -> let
        go (PipeM m) =
            PipeM $ catch (liftM go m) (\x -> return $ unConduit (onExc x) rest)
        go (Done r) = rest r
        go (Await p c) = Await (go . p) (go . c)
        go (Yield p m o) = Yield (go p) m o
        go (Leftover p i) = Leftover (go p) i

        in go (c0 Done)

-- | Await for a value from upstream.
await :: Conduit i o m (Maybe i)
await = Conduit $ \f -> Await (f . Just) (const (f Nothing))
{-# NOINLINE[1] await  #-}

await' :: Conduit i o m r
       -> (i -> Conduit i o m r)
       -> Conduit i o m r
await' f g = Conduit $ \rest -> Await
    (\i -> unConduit (g i) rest)
    (const $ unConduit f rest)
{-# INLINE await' #-}
{-# RULES "conduit: await >>= maybe" [2] forall x y. await >>= maybe x y = await' x y #-}

awaitForever :: (input -> Conduit input output monad b) -> Conduit input output monad ()
awaitForever f = Conduit $ \rest ->
    let go = Await (\i -> unConduit (f i) (const go)) rest
     in go

-- | Send a value downstream.
yield :: Monad m => o -> Conduit i o m ()
yield o = Conduit $ \f -> Yield (f ()) (return ()) o

-- | Same as 'yield', but additionally takes a finalizer to be run if
-- the downstream component terminates.
yieldOr :: o
        -> m () -- ^ finalizer
        -> Conduit i o m ()
yieldOr o m = Conduit $ \f -> Yield (f ()) m o

-- | Provide leftover input to be consumed by the next component in
-- the current monadic binding.
leftover :: i -> Conduit i o m ()
leftover i = Conduit $ \f -> Leftover (f ()) i

-- | Run a conduit pipeline to completion.
runConduit :: Monad m => Conduit () () m r -> m r
runConduit (Conduit f) = runPipe (f Done)

-- | Run a pure conduit pipeline to completion.
runConduitPure :: Conduit () () Identity r -> r
runConduitPure = runIdentity . runConduit

-- | Run a conduit pipeline in a 'ResourceT' context for acquiring resources.
runConduitRes :: (MonadBracket m, MonadIO m) => Conduit () () (ResourceT m) r -> m r
runConduitRes = runResourceT . runConduit

bracketConduit :: MonadResource m
               => IO a
               -> (a -> IO b)
               -> (a -> Conduit i o m r)
               -> Conduit i o m r
bracketConduit acquire cleanup inner = do
    (resource, release) <- allocate acquire cleanup
    result <- inner resource
    release
    return result

-- | Internal: run a @Pipe@
runPipe :: Monad m => Pipe () () () () m r -> m r
runPipe =
    go
  where
    go (Yield p _ ()) = go p
    go (Await _ p) = go (p ())
    go (Done r) = return r
    go (PipeM mp) = mp >>= go
    go (Leftover p ()) = go p

-- | Send the output of the first Conduit component to the second
-- Conduit component.
fuse :: Monad m => Conduit a b m () -> Conduit b c m r -> Conduit a c m r
fuse (Conduit left0) (Conduit right0) = Conduit $ \rest ->
    let goRight final left right =
            case right of
                Yield p c o       -> Yield (recurse p) (c >> final) o
                Await rp rc       -> goLeft rp rc final left
                Done r2           -> PipeM (final >> return (rest r2))
                PipeM mp          -> PipeM (liftM recurse mp)
                Leftover right' i -> goRight final (Yield left final i) right'
          where
            recurse = goRight final left

        goLeft rp rc final left =
            case left of
                Yield left' final' o -> goRight final' left' (rp o)
                Await left' lc       -> Await (recurse . left') (recurse . lc)
                Done r1              -> goRight (return ()) (Done r1) (rc r1)
                PipeM mp             -> PipeM (liftM recurse mp)
                Leftover left' i     -> Leftover (recurse left') i
          where
            recurse = goLeft rp rc final
     in goRight (return ()) (left0 Done) (right0 Done)

{- FIXME for later, if we add resourcet
-- | Safely acquire a resource and register a cleanup action for it,
-- in the context of a 'Conduit'.
bracketConduit :: MonadResource m
               => IO a -- ^ acquire
               -> (a -> IO ()) -- ^ cleanup
               -> (a -> Conduit i o m r)
               -> Conduit i o m r
bracketConduit alloc cleanup inner = Conduit $ \rest -> PipeM $ do
    (key, val) <- allocate alloc cleanup
    return $ unConduit (addCleanup (const $ release key) (inside seed)) rest

addCleanup :: Monad m
           => (Bool -> m ())
           -> Conduit i o m r
           -> Conduit i o m r
addCleanup cleanup (Conduit c0) = Conduit $ \rest -> let
    go (Done r) = PipeM (cleanup True >> return (rest r))
    go (Yield src close x) = Yield
        (go src)
        (cleanup False >> close)
        x
    go (PipeM msrc) = PipeM (liftM (go) msrc)
    go (Await p c) = Await
        (go . p)
        (go . c)
    go (Leftover p i) = Leftover (go p) i
    in go (c0 Done)
-}

newtype ZipSink i m r = ZipSink { getZipSink :: Conduit i () m r }

instance Monad m => Functor (ZipSink i m) where
    fmap f (ZipSink x) = ZipSink (liftM f x)
instance Monad m => Applicative (ZipSink i m) where
    pure  = ZipSink . return
    ZipSink (Conduit f0) <*> ZipSink (Conduit x0) =
      ZipSink $ Conduit $ \rest -> let
        go (Leftover _ i) _ = absurd i
        go _ (Leftover _ i) = absurd i
        go (Yield f _ ()) x = go f x
        go f (Yield x _ ()) = go f x
        go (PipeM mf) x = PipeM (liftM (`go` x) mf)
        go f (PipeM mx) = PipeM (liftM (go f) mx)
        go (Done f) (Done x) = rest (f x)
        go (Await pf cf) (Await px cx) = Await
            (\i -> go (pf i) (px i))
            (\() -> go (cf ()) (cx ()))
        go (Await pf cf) x@Done{} = Await
            (\i -> go (pf i) x)
            (\() -> go (cf ()) x)
        go f@Done{} (Await px cx) = Await
            (\i -> go f (px i))
            (\() -> go f (cx ()))

      in go (injectLeftovers (f0 Done)) (injectLeftovers (x0 Done))

data Void

absurd :: Void -> a
absurd _ = error "Foundation.Conduit.Internal.absurd"

injectLeftovers :: Monad m => Pipe i i o u m r -> Pipe l i o u m r
injectLeftovers =
    go []
  where
    go ls (Yield p c o) = Yield (go ls p) c o
    go (l:ls) (Await p _) = go ls $ p l
    go [] (Await p c) = Await (go [] . p) (go [] . c)
    go _ (Done r) = Done r
    go ls (PipeM mp) = PipeM (liftM (go ls) mp)
    go ls (Leftover p l) = go (l:ls) p

---------------------
-- ResourceT
---------------------
newtype ResourceT m a = ResourceT { unResourceT :: PrimVar IO ReleaseMap -> m a }
instance Functor m => Functor (ResourceT m) where
    fmap f (ResourceT m) = ResourceT $ \r -> fmap f (m r)
instance Applicative m => Applicative (ResourceT m) where
    pure = ResourceT . const . pure
    ResourceT mf <*> ResourceT ma = ResourceT $ \r ->
        mf r <*> ma r
instance Monad m => Monad (ResourceT m) where
#if !MIN_VERSION_base(4,8,0)
    return = ResourceT . const . return
#endif
    ResourceT ma >>= f = ResourceT $ \r -> do
        a <- ma r
        let ResourceT f' = f a
        f' r
instance MonadTrans ResourceT where
    lift = ResourceT . const
instance MonadIO m => MonadIO (ResourceT m) where
    liftIO = lift . liftIO
instance MonadThrow m => MonadThrow (ResourceT m) where
    throw = lift . throw
instance MonadCatch m => MonadCatch (ResourceT m) where
    catch (ResourceT f) g = ResourceT $ \env -> f env `catch` \e -> unResourceT (g e) env
instance MonadBracket m => MonadBracket (ResourceT m) where
    generalBracket acquire onSuccess onExc inner = ResourceT $ \env -> generalBracket
        (unResourceT acquire env)
        (\x y -> unResourceT (onSuccess x y) env)
        (\x y -> unResourceT (onExc x y) env)
        (\x -> unResourceT (inner x) env)

data ReleaseMap =
    ReleaseMap !NextKey !RefCount ![(Word, (ReleaseType -> IO ()))] -- FIXME use a proper Map?
  | ReleaseMapClosed

data ReleaseType = ReleaseEarly
                 | ReleaseNormal
                 | ReleaseException

type RefCount = Word
type NextKey = Word

runResourceT :: (MonadBracket m, MonadIO m) => ResourceT m a -> m a
runResourceT (ResourceT inner) = generalBracket
    (liftIO $ primVarNew $ ReleaseMap maxBound (minBound + 1) [])
    (\state _res -> liftIO $ cleanup state ReleaseNormal)
    (\state _exc -> liftIO $ cleanup state ReleaseException)
    inner
  where
    cleanup istate rtype = do
        mm <- atomicModifyIORef istate $ \rm ->
            case rm of
                ReleaseMap nk rf m ->
                    let rf' = rf - 1
                    in if rf' == minBound
                            then (ReleaseMapClosed, Just m)
                            else (ReleaseMap nk rf' m, Nothing)
                ReleaseMapClosed -> error "runResourceT: cleanup on ReleaseMapClosed"
        case mm of
            Just m -> mapM_ (\(_, x) -> ignoreExceptions (x rtype)) m
            Nothing -> return ()
      where
        ignoreExceptions io = void io `catch` (\(_ :: SomeException) -> return ())

allocate :: (MonadResource m, MonadIO n) => IO a -> (a -> IO b) -> m (a, n ())
allocate acquire release = liftResourceT $ ResourceT $ \istate -> liftIO $ mask_ $ do
    a <- acquire
    key <- atomicModifyIORef istate $ \rm ->
        case rm of
            ReleaseMap key rf m ->
                ( ReleaseMap (key - 1) rf ((key, const $ void $ release a) : m)
                , key
                )
            ReleaseMapClosed -> error "allocate: ReleaseMapClosed"
    let release' = join $ atomicModifyIORef istate $ \rm ->
            case rm of
                ReleaseMap nextKey rf m ->
                    let loop front [] = (ReleaseMap nextKey rf (front []), return ())
                        loop front ((key', action):rest)
                            | key == key' =
                                ( ReleaseMap nextKey rf (front rest)
                                , action ReleaseEarly
                                )
                            | otherwise = loop (front . ((key', action):)) rest
                     in loop id m
                ReleaseMapClosed -> error "allocate: ReleaseMapClosed (2)"
    return (a, liftIO release')

class MonadIO m => MonadResource m where
    liftResourceT :: ResourceT IO a -> m a
instance MonadIO m => MonadResource (ResourceT m) where
    liftResourceT (ResourceT f) = ResourceT (liftIO . f)
instance MonadResource m => MonadResource (Conduit i o m) where
    liftResourceT = lift . liftResourceT
