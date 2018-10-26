{-# LANGUAGE CPP #-}
module DoNothing.Plugin (plugin) where

#ifdef ghcjs_HOST_OS
import Plugins
#else
import GhcPlugins
#endif

#ifdef ghcjs_HOST_OS
plugin :: Plugin
plugin = error "The GHCJS build of DoNothing.Plugin cannot be used. Instead, build with GHC and use the result with GHCJS."
#else
plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install
  }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = do
  putMsgS "HELLO I AM A RUNNING PLUGIN!"
  return todo
#endif
