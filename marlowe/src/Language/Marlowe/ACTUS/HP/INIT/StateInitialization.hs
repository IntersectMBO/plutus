{-# LANGUAGE RecordWildCards #-}
module Language.Marlowe.ACTUS.HP.INIT.StateInitialization where

import Language.Marlowe.ACTUS.HP.ContractTerms
import Language.Marlowe.ACTUS.HP.ContractState
import Language.Marlowe.ACTUS.HP.INIT.PAM

inititializeState :: ContractTerms -> ContractState
inititializeState terms = case terms of
    PamContractTerms{..} -> ContractState{}