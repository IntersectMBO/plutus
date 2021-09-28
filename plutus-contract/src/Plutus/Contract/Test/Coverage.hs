module Plutus.Contract.Test.Coverage
  ( getInvocedEndpoints
  , getExecutedCoverageAnnotations
  ) where

import           Data.Map                    (Map)
import qualified Data.Map                    as Map
import           Data.Set                    (Set)
import qualified Data.Set                    as Set

import qualified Data.Text                   as Text
import           Text.Read

import           Control.Lens

import qualified Ledger

import           PlutusTx.Coverage

import           Plutus.Trace.Emulator.Types

import           Wallet.Emulator.Chain
import           Wallet.Emulator.MultiAgent  (EmulatorEvent, EmulatorEvent' (..), EmulatorTimeEvent (..), eteEvent)
import           Wallet.Types


-- | Get every endpoint name that has been invoced in the emulator events in `es`
-- indexed by `ContractInstanceTag`
getInvocedEndpoints :: [EmulatorEvent] -> Map ContractInstanceTag (Set String)
getInvocedEndpoints es =
  let cs = [ (view cilTag c, view cilMessage c) | EmulatorTimeEvent _ (InstanceEvent c) <- es ]
      t2ep = [ (t, ep) | (t, ReceiveEndpointCall (EndpointDescription ep) _) <- cs ]
      epsCovered = foldr (\(t, ep) -> Map.insertWith Set.union t (Set.singleton ep)) Map.empty t2ep
  in epsCovered

-- | Collect every executed coverage annotation in the validators executed in `es`
getExecutedCoverageAnnotations :: [EmulatorEvent] -> Set CoverageAnnotation
getExecutedCoverageAnnotations es =
  let extractLog e = case e of
        ChainEvent (TxnValidate _ _ valEvs)           -> logOf . Ledger.sveResult <$> valEvs
        ChainEvent (TxnValidationFail _ _ _ _ valEvs) -> logOf . Ledger.sveResult <$> valEvs
        _                                             -> []

      logOf (Left (Ledger.EvaluationError lg _)) = lg
      logOf (Left Ledger.EvaluationException{})  = []
      logOf (Left Ledger.MalformedScript{})      = []
      logOf (Right (_, lg))                      = lg

      validatorLogs = filter (Prelude.not . null) . concatMap (extractLog . view eteEvent) $ es

      readAndInsert msg anns = foldr Set.insert anns $ readMaybe $ Text.unpack $ msg

      coverageAnnotations = foldr readAndInsert Set.empty $ concat $ validatorLogs
  in coverageAnnotations
