module Language.Marlowe.ACTUS.HP.Applicability where

import Language.Marlowe.ACTUS.HP.ContractTerms

data PamContractTerms = PamContractTerms {
    nt :: Double
}

toGenericContractTerms :: PamContractTerms -> GenericContractTerms
toGenericContractTerms pam = GenericContractTerms {}