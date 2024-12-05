module Main (main) where

import Control.Monad (void)
import System.Directory (withCurrentDirectory)
import System.FilePath (dropExtensions, (<.>), (</>))
import System.Process (readProcess)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.Golden (findByExtension, goldenVsFile)

path :: String
path = "test/certifier"

package :: String
package = "plutus-executables"

mkTestCase :: FilePath -> TestTree
mkTestCase input =
    let expectedCert = dropExtensions input <.> "out" <.> "golden"
        actualCert = dropExtensions input <.> "out"
    in goldenVsFile input expectedCert actualCert (mkTest input actualCert)

mkTest :: FilePath -> FilePath -> IO ()
mkTest input testName = do
    -- This is a hack which is necessary because we rely on the
    -- PLUTUS_METHATHEORY_SRC environment variable
    withCurrentDirectory ".."
        $ void
        $ readProcess
            "uplc"
            [ "optimise"
            , "-i"
            , package </> input
            , "--certify"
            , package </> testName
            ]
            ""

main :: IO ()
main = do
    uplcFiles <- findByExtension [".uplc"] path
    defaultMain
        $ testGroup "certifier"
        $ mkTestCase
        <$> uplcFiles

