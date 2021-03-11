module Plutus.Contract.Util where

-- | A monadic version of 'loop', where the predicate returns 'Left' as a seed
--   for the next loop or 'Right' to abort the loop.
--
-- https://hackage.haskell.org/package/extra-1.6.15/docs/src/Control.Monad.Extra.html#loopM
loopM :: Monad m => (a -> m (Either a b)) -> a -> m b
loopM act x = do
    res <- act x
    case res of
        Left x' -> loopM act x'
        Right v -> return v

-- | Repeatedly evaluate the action until it yields 'Nothing',
--   then return the aggregated result.
foldMaybe
    :: Monad m
    => (a -> b -> b)
    -> b
    -> m (Maybe a)
    -> m b
foldMaybe f b con = loopM go b where
    go b' = maybe (Right b') (Left . flip f b') <$> con

-- | Monadic version of `<*`
finally :: Monad m => m a -> m b -> m a
finally a b = do
    a' <- a
    _ <- b
    return a'

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a  b c
