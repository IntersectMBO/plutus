{-

Define timeouts for IO actions

-}
module Plutus.PAB.Timeout (Timeout(..), startTimeout) where

import           Control.Concurrent     (forkIO, threadDelay)
import           Control.Concurrent.STM (TMVar)
import qualified Control.Concurrent.STM as STM
import           Control.Monad          (void)
import           Data.Default           (Default (..))
import           Data.Time.Units        (Second, toMicroseconds)

newtype Timeout = Timeout { unTimeout :: Maybe Second }

instance Default Timeout where
    def = Timeout Nothing

-- | Create a 'TMVar' that is filled when the timeout expires.
startTimeout :: Timeout -> IO (TMVar ())
startTimeout (Timeout Nothing) = STM.newTMVarIO ()
startTimeout (Timeout (Just s)) = do
    tmv <- STM.newEmptyTMVarIO
    void $ forkIO $ do
        threadDelay $ fromIntegral $ toMicroseconds s
        STM.atomically $ STM.putTMVar tmv ()
    pure tmv
