-- editorconfig-checker-disable-file
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoImplicitPrelude #-}

module PlutusLedgerApi.V3.ArbitraryContexts
  ( ArbitraryContext (..)
  , GovernanceAction (..)
  , FakeProposedContext (..)
  , mkFakeParameterChangeContext
  , mkFakeContextFromGovAction
  , mkLargeFakeProposal
  , mkSmallFakeProposal
  , memptyTxInfo
  , emptyRedeemer
  , simpleContextWithParam
  , withOneParamGen
  , treasuryWithdrawalsCtxGen
  ) where

import Cardano.Constitution.Config
import PlutusCore.Generators.QuickCheck ()
import PlutusLedgerApi.V3 as V3
import PlutusTx.AssocMap as AssocMap
import PlutusTx.AssocMap as Tx
import PlutusTx.Base as Tx
import PlutusTx.Builtins as Tx
import PlutusTx.IsData as Tx
import PlutusTx.Maybe as Tx
import PlutusTx.Monoid
import PlutusTx.NonCanonicalRational
import PlutusTx.Numeric
import PlutusTx.Ratio as Tx

import Codec.Serialise
import Control.Monad qualified as Haskell
import Data.Bifunctor qualified as Haskell
import Data.ByteString.Lazy qualified as BSL (length)
import Data.Function (on)
import Data.Int
import Data.List as List
import Data.String qualified as Haskell
import Test.Tasty.QuickCheck
import Prelude qualified as Haskell

-- | An arbitrary context, focusing mostly on generating proposals for changing parameters
newtype ArbitraryContext = ArbitraryContext
  { unArbitraryContext :: V3.ScriptContext
  }
  deriving newtype (Haskell.Show, Tx.ToData)

instance Arbitrary ArbitraryContext where
  arbitrary =
    ArbitraryContext
      Haskell.<$> ( V3.ScriptContext
                      Haskell.<$> arbitraryTxInfo
                      Haskell.<*> arbitraryRedeemer
                      Haskell.<*> arbitraryScriptInfo
                  )

arbitraryTxInfo :: Gen TxInfo
arbitraryTxInfo = Haskell.pure memptyTxInfo

arbitraryRedeemer :: Gen Redeemer
arbitraryRedeemer = Redeemer . BuiltinData Haskell.<$> arbitrary -- BuiltinData

memptyTxInfo :: TxInfo
memptyTxInfo =
  TxInfo
    { txInfoInputs = mempty
    , txInfoReferenceInputs = mempty
    , txInfoOutputs = mempty
    , txInfoFee = zero
    , txInfoMint = emptyMintValue
    , txInfoTxCerts = mempty
    , txInfoWdrl = AssocMap.unsafeFromList mempty
    , txInfoValidRange = always
    , txInfoSignatories = mempty
    , txInfoRedeemers = AssocMap.unsafeFromList mempty
    , txInfoData = AssocMap.unsafeFromList mempty
    , txInfoId = V3.TxId mempty
    , txInfoVotes = AssocMap.unsafeFromList mempty
    , txInfoProposalProcedures = mempty
    , -- cant'use mempty, Lovelace is not Semigroup
      txInfoCurrentTreasuryAmount = Nothing
    , -- cant'use mempty, Lovelace is not Semigroup
      txInfoTreasuryDonation = Nothing
    }

emptyRedeemer :: Redeemer
emptyRedeemer = Redeemer (toBuiltinData ())

arbitraryScriptInfo :: Gen ScriptInfo
arbitraryScriptInfo =
  frequency
    [ (1, Haskell.pure (MintingScript (V3.CurrencySymbol ""))) -- negative testing
    , (5, ProposingScript zero Haskell.<$> arbitraryProposalProcedure)
    ]

arbitraryProposalProcedure :: Gen ProposalProcedure
arbitraryProposalProcedure =
  ProposalProcedure zero
    Haskell.<$> arbitraryCredential
    Haskell.<*> arbitraryGovernanceAction

arbitraryCredential :: Gen Credential
arbitraryCredential = Haskell.pure (PubKeyCredential "")

arbitraryGovernanceAction :: Gen GovernanceAction
arbitraryGovernanceAction =
  ParameterChange Nothing
    Haskell.<$> arbitraryChangedParameters
    Haskell.<*> Haskell.pure Nothing

twAction :: Gen GovernanceAction
twAction =
  TreasuryWithdrawals
    Haskell.<$> treasuryWithdrawalsCredentials
    Haskell.<*> Haskell.pure Nothing

-- Define a generator for a single hexadecimal character
hexChar :: Gen Haskell.Char
hexChar = elements $ ['0' .. '9'] ++ ['a' .. 'f']

-- Define a generator for a hexadecimal string of a given length
hexString :: Int -> Gen Haskell.String
hexString len = Haskell.replicateM len hexChar

-- Generate a list of arbitrary length hexadecimal strings
arbitraryHexStrings :: Gen [(Credential, Lovelace)]
arbitraryHexStrings = sized $ \n -> do
  k <- choose (0, n) -- Generate a length for the list
  let toCredential = Haskell.map (PubKeyCredential . Haskell.fromString)
  str <- toCredential Haskell.<$> vectorOf k (hexString 16) -- Generate a list of hex strings
  int <- Haskell.map Lovelace Haskell.<$> vectorOf k (chooseInteger (1, 100000000)) -- Generate a list of integers
  Haskell.pure $ zip str int

treasuryWithdrawalsCredentials :: Gen (Map Credential Lovelace)
treasuryWithdrawalsCredentials = do
  unsafeFromList Haskell.<$> arbitraryHexStrings

treasuryWithdrawalsCtxGen :: Gen ScriptContext
treasuryWithdrawalsCtxGen =
  V3.ScriptContext
    Haskell.<$> arbitraryTxInfo
    Haskell.<*> arbitraryRedeemer
    Haskell.<*> twInfo

twInfo :: Gen ScriptInfo
twInfo = ProposingScript zero Haskell.<$> twProposalProcedure

twProposalProcedure :: Gen ProposalProcedure
twProposalProcedure =
  ProposalProcedure zero
    Haskell.<$> arbitraryCredential
    Haskell.<*> twAction

arbitraryChangedParameters :: Gen ChangedParameters
arbitraryChangedParameters =
  ChangedParameters
    Haskell.<$> frequency
      [ (1, Haskell.pure (Tx.toBuiltinData (Tx.mkList []))) -- negative testing
      , (1, Haskell.pure (Tx.toBuiltinData (Tx.mkI zero))) -- negative testing
      -- See guarantees (2) and (3) in README.md
      ,
        ( 10
        , Tx.toBuiltinData
            -- sort the random Map, see guarantee (3) in README.md
            -- Ugly code, but we want to use an external sorting function here (GHC stdlib)
            -- because we do not want to rely for our tests on
            -- our experimental `PlutusTx.SortedMap` sorting functions.
            -- NOTE: do not use safeFromList; it destroys sortedness.
            . AssocMap.unsafeFromList
            . List.sortOn fst
            . AssocMap.toList
            -- using safeFromList here de-deduplicates the Map,
            -- See guarantee (2) in README.md
            -- See Note [Why de-duplicated ChangedParameters]
            . AssocMap.safeFromList
            Haskell.<$> listOf arbitraryChangedParameter
        )
      ]

arbitraryChangedParameter :: Gen (ParamKey, BuiltinData)
arbitraryChangedParameter =
  (,)
    -- TODO: this is too arbitrary, create more plausible keys
    Haskell.<$> arbitrary
    Haskell.<*> arbitraryParamValue
  where
    arbitraryParamValue :: Gen BuiltinData
    arbitraryParamValue =
      frequency
        [ (2, arbitraryLeaf)
        , (1, arbitraryNode) -- testing subs
        ]
      where
        arbitraryLeaf =
          oneof
            [ -- TODO: this is too arbitrary, create more plausible values
              Tx.toBuiltinData Haskell.<$> arbitrary @Integer
            , -- TODO: this is too arbitrary, create more plausible values
              Haskell.fmap (Tx.toBuiltinData . NonCanonicalRational) . Tx.unsafeRatio
                Haskell.<$> arbitrary
                -- unsafeRatio err's on zero denominator
                Haskell.<*> arbitrary `suchThat` (Haskell./= 0)
            ]
        -- 1-level nested, arbitrary-level can become too expensive
        arbitraryNode = Tx.toBuiltinData Haskell.<$> listOf arbitraryLeaf

-- | An arbitrary context, focusing mostly on generating proposals for changing parameters
newtype FakeProposedContext = FakeProposedContext
  { unFakeProposedContext :: V3.ScriptContext
  }
  deriving newtype (Haskell.Show, ToData)

{-| Make a fake proposed context given some changed parameters.
It keeps a) the order of pairs in the input and b) any duplicates in the input list.
Thus it can be used only for testing purposes.
In reality, the ledger guarantees sorted *AND* de-duped ChangedParams. -}
mkFakeParameterChangeContext :: ToData b => [(ParamKey, b)] -> FakeProposedContext
mkFakeParameterChangeContext =
  mkFakeContextFromGovAction
    . flip (V3.ParameterChange Nothing) Nothing
    . V3.ChangedParameters
    . Tx.toBuiltinData
    -- this is the unsafe version so we can test duplicates also.
    -- NOTE: do not use safeFromList; it destroys sortedness.
    . AssocMap.unsafeFromList

mkFakeContextFromGovAction :: V3.GovernanceAction -> FakeProposedContext
mkFakeContextFromGovAction =
  FakeProposedContext
    . V3.ScriptContext memptyTxInfo emptyRedeemer
    . V3.ProposingScript 0
    . V3.ProposalProcedure 0 (V3.PubKeyCredential "")

simpleContextWithParam :: forall a. ToData a => [(ParamKey, a)] -> ArbitraryContext
simpleContextWithParam param = ArbitraryContext scriptContext
  where
    scriptContext = V3.ScriptContext memptyTxInfo emptyRedeemer arbitraryScriptInfo'

    arbitraryScriptInfo' :: ScriptInfo
    arbitraryScriptInfo' = ProposingScript zero arbitraryProposalProcedure'

    arbitraryProposalProcedure' :: ProposalProcedure
    arbitraryProposalProcedure' = ProposalProcedure zero (PubKeyCredential "") arbitraryGovernanceAction'

    arbitraryGovernanceAction' :: GovernanceAction
    arbitraryGovernanceAction' = ParameterChange Nothing paramChange Nothing

    paramChange = ChangedParameters (Tx.toBuiltinData . Tx.unsafeFromList $ param)

withOneParamGen :: ToData a => Gen (ParamKey, a) -> Gen ArbitraryContext
withOneParamGen gen = do
  a <- gen
  Haskell.pure $ simpleContextWithParam [a]

mkLargeFakeProposal, mkSmallFakeProposal :: ConstitutionConfig -> FakeProposedContext

{-| Constructs a large proposal, that proposes to change *every parameter* mentioned in the given config.

This proposal will most likely be accepted by the Validators, see `mkChangedParamsFromMinValues`.

We want this for budget-testing the WORST-CASE scenario. -}

-- TODO: replaced by Guardrails.getFakeLargeParamsChange
-- ( we can't use it here because of the circular dependency )
mkLargeFakeProposal = mkFakeParameterChangeContext . mkChangedParamsFromMinValues

{-| Constructs a small proposal, that proposes to change *only one parameter* (the first one) mentioned in the given config.

This proposal will most likely be accepted by the Validators, see `mkChangedParamsFromMinValues`.

We want this for budget-testing the BEST-CASE scenario. We cannot use an empty proposal,
because all ConstitutionValidators guard *against* empty proposals, so they will never pass and be rejected very early. -}
mkSmallFakeProposal =
  mkFakeParameterChangeContext
    . Haskell.pure
    -- arbitrary choose one parameter keyvalue that is the smallest in serialised size
    -- this does not necessary lead to smallest execution time, but it is just more explicitly defined than using `head`
    . minimumBy (Haskell.compare `on` (BSL.length . serialise . toData))
    . mkChangedParamsFromMinValues

{-| This is is used to construct a LARGE ChangedParams.

It does so by transforming the give constitution config to a Fake Proposal, using this arbitrary method:

- take the LARGEST `minValue` number (integer or rational) for each (sub-)parameter.
- if a `minValue` predicate is missing, use a `def`ault 0 (if Integer), 0/1 if Rational.

If this ChangedParams is inputted to a ConstitutionValidator, it will most likely result into a successful execution.
"Most likely" because, the chosen value may interfere with other predicates (notEqual, maxValue). -}
mkChangedParamsFromMinValues :: ConstitutionConfig -> [(ParamKey, BuiltinData)]
mkChangedParamsFromMinValues = Haskell.fmap (Haskell.second getLargestMinValue) . unConstitutionConfig
  where
    getLargestMinValue :: ParamValue -> BuiltinData
    getLargestMinValue = \case
      ParamInteger preds -> toBuiltinData $ maximum $ fromMaybe [0] $ List.lookup MinValue $ unPredicates preds
      ParamRational preds -> toBuiltinData $ NonCanonicalRational $ maximum $ fromMaybe [Tx.unsafeRatio 0 1] $ List.lookup MinValue $ unPredicates preds
      ParamList values -> toBuiltinData $ Haskell.fmap getLargestMinValue values
      -- Currently we only have param 18 as "any". So this generation applies only for 18.
      -- Here we try to generate an 1000-integer-list for the 18 parameter.
      -- Note: This is not the correct encoding of the 18 parameter, it is only for simulating a large size of proposal.
      -- Even with a wrong encoding, it will be accepted by the constitution script,
      -- because "any" in the config means accept any encoding: the script does not check the encoding at all.
      ParamAny -> toBuiltinData $ replicate 1000 (Haskell.toInteger $ Haskell.maxBound @Int64)
