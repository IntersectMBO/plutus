{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE InstanceSigs        #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}

module Control.Concurrent.STM.Extras.Stream
  ( STMStream
  , readOne
  , readN
  , foldM
  , unfold
  , singleton
  , dedupe
  ) where

import           Control.Applicative    (Alternative (..), Applicative (..))
import           Control.Concurrent.STM (STM)
import qualified Control.Concurrent.STM as STM
import           Control.Monad          (guard)
import           Data.Bifunctor         (Bifunctor (..))
import           Data.Foldable          (traverse_)
import           Numeric.Natural        (Natural)

-- | An STM stream of 'a's (poor man's pull-based FRP)
newtype STMStream a = STMStream{ unSTMStream :: STM (a, Maybe (STMStream a)) }
    deriving Functor

-- | Join a stream of streams by producing values from the latest stream only.
joinStream :: STMStream (STMStream a) -> STMStream a
joinStream STMStream{unSTMStream} = STMStream $ unSTMStream >>= go where

    go :: (STMStream a, Maybe (STMStream (STMStream a))) -> STM (a, Maybe (STMStream a))
    go (STMStream currentStream, Nothing) = currentStream
    go (STMStream currentStream, Just ns@(STMStream nextStream)) = do
        vl <- fmap Left currentStream <|> fmap Right nextStream
        case vl of
            Left (a, Just currentStream') -> pure (a, Just $ STMStream $ go (currentStream', Just ns))
            Left (a, Nothing)             -> pure (a, Just $ joinStream ns)
            Right ns'                     -> go ns'

-- | Build a stream containing only one element.
singleton :: STM a -> STMStream a
singleton = STMStream . fmap (, Nothing)

instance Applicative STMStream where
    pure = singleton . pure
    -- | Updates when one of the two sides updates
    liftA2 :: forall a b c. (a -> b -> c) -> STMStream a -> STMStream b -> STMStream c
    liftA2 f (STMStream l) (STMStream r) = STMStream $ do
        x <- (,) <$> l <*> r
        let go :: ((a, Maybe (STMStream a)), (b, Maybe (STMStream b))) -> STM (c, Maybe (STMStream c))

            go ((currentL, Just (STMStream restL)), (currentR, Just (STMStream restR))) = do
                let next = do
                        v <- fmap Left restL <|> fmap Right restR
                        case v of
                            Left (newL, restL')  -> go ((newL, restL'), (currentR, Just $ STMStream restR))
                            Right (newR, restR') -> go ((currentL, Just $ STMStream restL), (newR, restR'))
                pure (f currentL currentR, Just $ STMStream next)
            go ((currentL, Just (STMStream restL)), (currentR, Nothing)) =
                let apply = flip f currentR in
                pure (f currentL currentR, Just $ STMStream $ fmap (first apply . second (fmap (fmap apply))) restL)
            go ((currentL, Nothing), (currentR, Just (STMStream restR))) =
                let apply = f currentL in
                pure (f currentL currentR, Just $ STMStream $ fmap (first apply . second (fmap (fmap apply))) restR)
            go ((currentL, Nothing), (currentR, Nothing)) =
                pure (f currentL currentR, Nothing)
        go x

instance Monad STMStream where
    x >>= f = joinStream (f <$> x)

instance Eq a => Semigroup (STMStream a) where
  -- Note: We remove consecutive duplicates from the stream, so it is now
  -- never possible to construct a stream like: 1,1,1,1...
  ls@(STMStream l) <> rs@(STMStream r) = dedupe $
     STMStream $ do
          next <- fmap Left l <|> fmap Right r
          case next of
            Left  (v, k) -> pure (v, k <> Just rs)
            Right (v, k) -> pure (v, Just ls <> k)

instance Eq a => Monoid (STMStream a) where
    mappend = (<>)
    mempty = STMStream STM.retry

-- | Remove consecutive duplicates from a stream.
dedupe :: forall a. Eq a => STMStream a -> STMStream a
dedupe = STMStream . go Nothing
  where
    go :: Maybe a -> STMStream a -> STM (a, Maybe (STMStream a))
    go lastVl (STMStream s) = do
      (next, ms) <- s
      case ms of
        Nothing -> pure (next, Nothing)
        Just s' ->
          if Just next /= lastVl
             then pure (next, Just $ STMStream $ go (Just next) s')
             else go lastVl s'

-- | Produce an infinite stream of values from an STM (i.e. watch it for
-- updates). Uses the Eq instances to not output the same value twice in a
-- row.
unfold :: forall a. Eq a => STM a -> STMStream a
unfold tx = STMStream $ go Nothing where
    go :: Maybe a -> STM (a, Maybe (STMStream a))
    go lastVl = do
        next <- tx
        traverse_ (\previous -> guard (previous /= next)) lastVl
        pure (next, Just $ STMStream $ go (Just next))

-- | Read the first event from the stream.
readOne :: STMStream a -> IO (a, Maybe (STMStream a))
readOne STMStream{unSTMStream} = STM.atomically unSTMStream

-- | Read a number of events from the stream. Blocks until all events
--   have been received.
readN :: Natural -> STMStream a -> IO [a]
readN 0 _ = pure []
readN k s = do
    (a, s') <- readOne s
    case s' of
        Nothing   -> pure [a]
        Just rest -> (:) a <$> readN (pred k) rest

-- | Consume a stream. Blocks until the stream has terminated.
foldM ::
    STMStream a -- ^ The stream
    -> (a -> IO ()) -- ^ Event handler
    -> IO () -- ^ Handler for the end of the stream
    -> IO ()
foldM s handleEvent handleStop = do
    (v, next) <- readOne s
    handleEvent v
    case next of
        Nothing -> handleStop
        Just s' -> foldM s' handleEvent handleStop
