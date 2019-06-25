module Spec.Lib(reasonable, goldenPir) where

import           Control.Monad.IO.Class    (MonadIO (liftIO))
import           Test.Tasty
import           Test.Tasty.Golden
import           Test.Tasty.HUnit

import           Data.Maybe
import           Data.String
import           Data.Text.Prettyprint.Doc

import           Language.PlutusTx
import           Ledger                    (ValidatorScript)
import qualified Ledger

-- | Assert that the size of a 'ValidatorScript' is below
--   the maximum.
reasonable :: ValidatorScript -> Integer -> Assertion
reasonable (Ledger.ValidatorScript s) maxSize = do
    let sz = Ledger.scriptSize s
        msg = "Script too big! Max. size: " <> show maxSize <> ". Actual size: " <> show sz
    -- so the actual size is visible in the log
    liftIO $ putStrLn ("Script size: " ++ show sz)
    assertBool msg (sz <= maxSize)

goldenPir :: FilePath -> CompiledCode a -> TestTree
goldenPir path code = goldenVsString "PIR" path (pure $ fromString $ show $ pretty $ fromJust $ getPir code)
