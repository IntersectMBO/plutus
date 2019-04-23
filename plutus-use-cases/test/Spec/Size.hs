module Spec.Size(reasonable) where

import           Control.Monad.IO.Class (MonadIO (liftIO))
import qualified Test.Tasty.HUnit       as HUnit

import           Ledger                 (ValidatorScript)
import qualified Ledger

-- | Assert that the size of a 'ValidatorScript' is below
--   the maximum.
reasonable :: ValidatorScript -> Integer -> HUnit.Assertion
reasonable (Ledger.ValidatorScript s) maxSize = do
    let sz = Ledger.scriptSize s
        msg = "Script too big! Max. size: " <> show maxSize <> ". Actual size: " <> show sz
    -- so the actual size is visible in the log
    liftIO $ putStrLn ("Script size: " ++ show sz)
    HUnit.assertBool msg (sz <= maxSize)
