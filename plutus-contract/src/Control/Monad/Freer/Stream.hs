{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

{- Interpreting the 'Yield' effect as a stream -}
module Control.Monad.Freer.Stream(
    runStream
    ) where

import           Control.Monad.Freer
import           Control.Monad.Freer.Coroutine (Status (..), Yield, runC)
import           Streaming                     (Stream)
import           Streaming.Prelude             (Of)
import qualified Streaming.Prelude             as S

-- | Turn the @Yield e ()@ effect into a pull-based stream
--   of @e@ events.
runStream :: forall e a effs.
    Eff (Yield e () ': effs) a
    -> Stream (Of e) (Eff effs) a
runStream action =
    let f :: Eff effs (Status effs e () a) -> Eff effs (Either a (e, Eff effs (Status effs e () a)))
        f a = do
            result <- a
            case result of
                Done b          -> pure (Left b)
                Continue e cont -> pure $ Right (e, cont ())
    in S.unfoldr f (runC action)
