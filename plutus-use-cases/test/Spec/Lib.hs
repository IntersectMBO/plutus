{-# LANGUAGE ViewPatterns #-}
module Spec.Lib
    ( reasonable
    , goldenPir
    , timesFeeAdjust
    , timesFeeAdjustV
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
import qualified Ledger.Ada                as Ada
import           Ledger.Value              (Value)
import           PlutusTx
import qualified PlutusTx.Prelude          as P

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

staticFee :: Integer
staticFee = Ada.getLovelace . Ada.fromValue . Ledger.minFee $ mempty

-- | Deduct transaction fees from wallet funds, and make
--   the fee amount explicit in the test specification
timesFeeAdjust :: Integer -> Integer -> Value
timesFeeAdjust multiplier change =
    timesFeeAdjustV multiplier (Ada.lovelaceValueOf change)

-- | Deduct transaction fees from wallet funds, and make
--   the fee amount explicit in the test specification
timesFeeAdjustV :: Integer -> Value -> Value
timesFeeAdjustV multiplier change =
    change P.- Ada.lovelaceValueOf (staticFee * multiplier)
