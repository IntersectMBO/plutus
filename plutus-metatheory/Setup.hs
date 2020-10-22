{-# LANGUAGE OverloadedStrings #-}
import           Data.Functor
import           Distribution.Simple
import           Distribution.Simple.Setup
import           Distribution.Types.HookedBuildInfo
import           Distribution.Types.LocalBuildInfo
import           Distribution.Types.PackageDescription
import           Turtle

main :: IO ()
main = defaultMainWithHooks userhooks

userhooks :: UserHooks
userhooks = simpleUserHooks {
      postConf = \_ _ _ _ -> runAgda
    , preBuild = \_ _ -> runAgda >> pure emptyHookedBuildInfo
    }

{- Note [Cabal hooks for Agda]
We want to run Agda to generate some of the Haskell sources for this project.

We do this with cabal hooks. The considerations are:
- We need it to run before Haddock also
- We want the Haskell to be regenerated if the Agda has changed before building the
Haskell.

This is tricky: the first point suggests having a post-configure hook, but then the
second won't work, since Cabal won't detect that it needs to reconfigure if the
Agda changes.

The only way is to rely on Agda to do the change detection, and run it every time.
That means we need a pre-build hook. But then it won't run before Haddock!

So: we do both! Since Agda is reasonably good at not redoing work, we mostly don't
pay the cost twice on the first configure/build sequence.
-}

postConf' :: Args -> ConfigFlags -> PackageDescription -> LocalBuildInfo -> IO ()
postConf' _ _ _ _ = runAgda

-- This adds a pre-build hook which calls Agda. No attempt is made to fail gracefully.
-- Doing this before building ensures that the generated Haskell files are always up-to-date, since cabal won't
-- track the dependency on the source Agda files, but Agda should do
preBuild' :: Args -> BuildFlags -> IO ()
preBuild' _ _ = runAgda

runAgda :: IO ()
runAgda = procs "agda" ["--compile", "--ghc-dont-call-ghc", "--local-interfaces", "src/Main.lagda"] empty
