{-# LANGUAGE OverloadedStrings #-}
import           Distribution.Simple
import           Distribution.Simple.Setup
import           Distribution.Types.HookedBuildInfo
import           Turtle

main :: IO ()
main = defaultMainWithHooks userhooks

userhooks :: UserHooks
userhooks = simpleUserHooks { preBuild = preBuild' }

-- This adds a pre-build hook which calls Agda. No attempt is made to fail gracefully.
-- Pre-build seems like the right place, post-configure could also be plausible, but I'm not really sure.
preBuild' :: Args -> BuildFlags -> IO HookedBuildInfo
preBuild' _ _ = do
    proc "agda" ["--compile", "--ghc-dont-call-ghc", "--local-interfaces", "Main.lagda"] empty
    pure emptyHookedBuildInfo
