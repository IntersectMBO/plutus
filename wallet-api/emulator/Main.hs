module Main where

import           Control.Concurrent.STM   (atomically, newTVar)
import qualified Data.HashMap.Strict      as HM
import           Network.Wai.Handler.Warp (run)
import           Wallet.Emulator.Http     (State (State), app)

main :: IO ()
main = do
  putStrLn "start emulator"
  initialState <- atomically $ newTVar HM.empty
  let state = State initialState
  run 8080 $ app state
