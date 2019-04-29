module Main where

import           Network.Wai.Handler.Warp (run)
import           Wallet.Emulator.Http     (app, initialState)

main :: IO ()
main = do
  putStrLn "start emulator"
  state <- initialState
  run 8080 $ app state
