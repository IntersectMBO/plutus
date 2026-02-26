module LuitePlugin (plugin) where

import GHC.Plugins

plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install
  }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = {-# SCC plugin_install #-} do
  putMsgS ("Hello! " ++ show (fib 40))
  return todo

fib :: Integer -> Integer
fib 0 = 0
fib 1 = 1
fib n = fib (n-2) + fib (n-1)