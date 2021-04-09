{-# LANGUAGE ViewPatterns #-}
module Spec.Lib
    ( reasonable
    , goldenPir
    ) where

import           Control.Monad.IO.Class    (MonadIO (liftIO))
import           Test.Tasty
import           Test.Tasty.Golden
import           Test.Tasty.HUnit

import           Data.Maybe
import           Data.String
import           Data.Text.Prettyprint.Doc

import           Ledger                    (Validator)
import qualified Ledger
import           PlutusTx

-- | Assert that the size of a 'Validator' is below
--   the maximum.
reasonable :: Validator -> Integer -> Assertion
reasonable (Ledger.unValidatorScript -> s) maxSize = do
    let sz = Ledger.scriptSize s
        msg = "Script too big! Max. size: " <> show maxSize <> ". Actual size: " <> show sz
    -- so the actual size is visible in the log
    liftIO $ putStrLn ("Script size: " ++ show sz)
    assertBool msg (sz <= maxSize)

goldenPir :: FilePath -> CompiledCode a -> TestTree
goldenPir path code = goldenVsString "PIR" path (pure $ fromString $ show $ pretty $ fromJust $ getPir code)
