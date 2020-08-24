{-# LANGUAGE OverloadedStrings #-}
import           Data.Functor
import           Distribution.Simple
import           Distribution.Simple.Setup
import           Distribution.Types.LocalBuildInfo
import           Distribution.Types.PackageDescription
import           Turtle

main :: IO ()
main = defaultMainWithHooks userhooks

userhooks :: UserHooks
userhooks = simpleUserHooks { postConf = postConf' }

-- This adds a post-configure hook which calls Agda. No attempt is made to fail gracefully.
-- Post-configure seems like the right place, so it runs even if we're doing a non-build thing like Haddock.
postConf' :: Args -> ConfigFlags -> PackageDescription -> LocalBuildInfo -> IO ()
postConf' _ _ _ _ = void $ proc "agda" ["--compile", "--ghc-dont-call-ghc", "--local-interfaces", "src/Main.lagda"] empty
