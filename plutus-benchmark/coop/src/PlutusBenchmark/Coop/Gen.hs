{- The code here is shamelessly stolen from [mlabs-haskell/cardano-open-oracle-protocol](https://github.com/mlabs-haskell/cardano-open-oracle-protocol/blob/main/coop-plutus/test/Coop/Plutus/Test/Generators.hs).
Note for benchmarking execution unit, one should not use this generators on benchmark cases. These
script context generators are to be used as one-off to generate one script context which is to be used
on every runs of the benchmark. It is important to understand changing script context will change
execution unit.
-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module PlutusBenchmark.Coop.Gen where

import Test.QuickCheck
  ( Arbitrary (arbitrary)
  , Gen
  , choose
  , chooseAny
  , chooseEnum
  , chooseInt
  , chooseInteger
  , sublistOf
  , suchThat
  , vectorOf
  )

import Control.Monad (foldM, replicateM)
import Crypto.Hash (Blake2b_256 (Blake2b_256), hashWith)
import Data.ByteArray (convert)
import Data.ByteString (ByteString, cons)
import Data.Foldable (Foldable (fold))
import Data.List (sort, sortOn)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Traversable (for)
import PlutusLedgerApi.V1.Address (pubKeyHashAddress, scriptHashAddress)
import PlutusLedgerApi.V1.Value
import PlutusLedgerApi.V2 hiding (Map)
import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.Builtins.HasOpaque (stringToBuiltinByteString)

import PlutusBenchmark.Coop.Types
import PlutusLedgerApi.V1.Interval (interval)
import PlutusLedgerApi.V2 qualified as Value
import PlutusTx.Prelude (Group (inv))

mkScriptContext :: ScriptPurpose -> [TxInInfo] -> [TxInInfo] -> Value -> [TxOut] -> [PubKeyHash] -> ScriptContext
mkScriptContext purpose ins refs mints outs sigs =
  ScriptContext (mkTxInfo ins refs mints outs sigs) purpose

mkTxInfo :: [TxInInfo] -> [TxInInfo] -> Value -> [TxOut] -> [PubKeyHash] -> TxInfo
mkTxInfo ins refs mints outs sigs =
  TxInfo
    { txInfoFee = mempty
    , txInfoDCert = mempty
    , txInfoWdrl = AssocMap.empty
    , txInfoValidRange = always
    , txInfoData = AssocMap.empty
    , txInfoId = ""
    , txInfoRedeemers = AssocMap.empty
    , txInfoInputs = sortOn (\(TxInInfo i _) -> i) ins
    , txInfoReferenceInputs = sortOn (\(TxInInfo i _) -> i) refs
    , txInfoMint = normalizeValue mints
    , txInfoOutputs = outs
    , txInfoSignatories = sigs
    }

setValidity :: ScriptContext -> Value.POSIXTimeRange -> ScriptContext
setValidity ctx validity =
  ctx
    { scriptContextTxInfo =
        (scriptContextTxInfo ctx)
          { txInfoValidRange = validity
          }
    }

genAaInputs :: AssetClass -> Integer -> Gen [TxInInfo]
genAaInputs aaAc aaQ = do
  aaTokens <- choose (aaQ, aaQ + 10) >>= \n -> return $ replicate (fromInteger n) . assetClassValue aaAc $ 1
  aaWallets <- choose (1, length aaTokens) >>= \n -> for [1 .. n] $ \ix -> return . pubKeyHashAddress . PubKeyHash . stringToBuiltinByteString $ "pubkeyhash " <> show ix
  aaOrefs <- choose (1, length aaTokens) >>= \n -> for [1 .. n] $ \ix -> return $ TxOutRef (TxId $ "transaction " <> (stringToBuiltinByteString . show $ ix)) (toInteger ix)
  aaOrefsWithTokens <- fmap fold <$> distribute aaTokens (Set.fromList aaOrefs)
  aaWalletsWithOrefs <- distribute aaOrefs (Set.fromList aaWallets)
  let aaOutsByAddr =
        ( \orefs -> do
            oref <- orefs
            maybe
              []
              (\tokens -> return (oref, tokens))
              $ Map.lookup oref aaOrefsWithTokens
        )
          <$> aaWalletsWithOrefs

  for
    [(addr, oref, val) | (addr, outs) <- Map.toList aaOutsByAddr, (oref, val) <- outs, assetClassValueOf val aaAc > 0]
    $ \(addr, oref, val) -> return $ TxInInfo oref (TxOut addr val NoOutputDatum Nothing)

toOutputDatum :: ToData a => a -> OutputDatum
toOutputDatum = OutputDatum . Datum . toBuiltinData

genCertRdmrInputs :: AssetClass -> Gen [TxInInfo]
genCertRdmrInputs certRdmrAc = do
  nCertRdmrInputs <- chooseInt (1, 10)
  certRdmrAddrs <- replicateM nCertRdmrInputs genAddress
  return
    [ TxInInfo
        (TxOutRef (TxId "$CERT-RDMR input") 0)
        ( TxOut
            addr
            (assetClassValue certRdmrAc 1)
            NoOutputDatum
            Nothing
        )
    | addr <- certRdmrAddrs
    ]

genCertInput :: Address -> CurrencySymbol -> AssetClass -> Interval POSIXTime -> BuiltinByteString -> Gen TxInInfo
genCertInput certVAddr certCs certRdmrAc certValidity certId = do
  return $
    TxInInfo
      (TxOutRef (TxId certId) 0)
      ( TxOut
          certVAddr
          (Value.singleton certCs (TokenName certId) 1)
          (toOutputDatum $ CertDatum (LedgerBytes certId) certValidity certRdmrAc)
          Nothing
      )

genCertInputs :: Address -> CurrencySymbol -> AssetClass -> Interval POSIXTime -> Gen [TxInInfo]
genCertInputs certVAddr certCs certRdmrAc validity = do
  nCertInputs <- chooseInt (1, 10)
  certIds <- replicateM nCertInputs genAuthenticatonId
  for certIds (genCertInput certVAddr certCs certRdmrAc validity)

genAuthInput :: CurrencySymbol -> BuiltinByteString -> Gen TxInInfo
genAuthInput authCs authId = do
  authQ <- chooseInteger (1, 10)
  authWallet <- genAddress
  return $
    TxInInfo
      (TxOutRef (TxId authId) 0)
      ( TxOut
          authWallet
          (Value.singleton authCs (TokenName authId) authQ)
          NoOutputDatum
          Nothing
      )

genAuthInputs :: CurrencySymbol -> Gen [TxInInfo]
genAuthInputs authCs = do
  nAuthInputs <- chooseInt (1, 10)
  authIds <- replicateM nAuthInputs genAuthenticatonId
  authQs <- replicateM nAuthInputs (chooseInteger (1, 10))
  authWallets <- replicateM 5 genAddress
  authWalletsWithIdsAndQs <- distribute (zip authIds authQs) $ Set.fromList authWallets

  let authInputs =
        ( \(authWallet, authId, authQ) ->
            TxInInfo
              (TxOutRef (TxId authId) 0)
              ( TxOut
                  authWallet
                  (Value.singleton authCs (TokenName authId) authQ)
                  NoOutputDatum
                  Nothing
              )
        )
          <$> [(authWallet, authId, authQ) | (authWallet, idsAndQs) <- Map.toList authWalletsWithIdsAndQs, (authId, authQ) <- idsAndQs]
  return authInputs

genCertRdmrAc :: Gen AssetClass
genCertRdmrAc = do
  certRdmrCs <- genCurrencySymbol
  return $ assetClass certRdmrCs (TokenName "$CERT-RDMR TN")

genCorrectCertMpMintingCtx :: CertMpParams -> CurrencySymbol -> Gen ScriptContext
genCorrectCertMpMintingCtx certMpParams certCs = do
  let aaAc = cmp'authAuthorityAc certMpParams
      aaQ = cmp'requiredAtLeastAaQ certMpParams
      certVAddr = cmp'certVAddress certMpParams
  aaIns <- genAaInputs aaAc aaQ
  certRdmrAc <- genCertRdmrAc
  (otherIns, otherMint, otherOuts) <- genOthers 5
  let certId = toBuiltin . hashTxInputs $ aaIns
      certTn = TokenName certId
      certToken = assetClassValue (assetClass certCs certTn) 1
      certDatum = CertDatum (LedgerBytes certId) (interval 0 100) certRdmrAc
      certOut = TxOut certVAddr certToken (OutputDatum . Datum . toBuiltinData $ certDatum) Nothing
      ins = otherIns <> aaIns
      mint = otherMint <> certToken
      outs = otherOuts <> [certOut]
  return $
    mkScriptContext (Minting certCs) ins [] mint outs []

genCorruptCertMpMintingCtx :: CertMpParams -> CurrencySymbol -> Gen ScriptContext
genCorruptCertMpMintingCtx certMpParams certCs = do
  let certVAddr = cmp'certVAddress certMpParams

  ctx <- genCorrectCertMpMintingCtx certMpParams certCs

  otherAddr <- genAddress
  -- Randomly pick corruptions
  corruptions <-
    suchThat
      ( sublistOf
          [ doMintAndPayOtherTokenName certCs
          , doRemoveOutputDatum
          , doPayToOtherAddress certVAddr otherAddr
          ]
      )
      (not . null)

  let corrupt = mkCorrupt corruptions

  return $ corrupt ctx

genValidity :: Gen (Interval POSIXTime)
genValidity = chooseInteger (0, 50) >>= \l -> chooseInteger (l, 100) >>= \u -> return $ interval (POSIXTime l) (POSIXTime u)

genCorrectCertMpBurningCtx :: CertMpParams -> CurrencySymbol -> AssetClass -> Gen ScriptContext
genCorrectCertMpBurningCtx certMpParams certCs certRdmrAc = do
  let certVAddr = cmp'certVAddress certMpParams
  certValidity <- genValidity
  certIns <- genCertInputs certVAddr certCs certRdmrAc certValidity
  certRdmrIns <- genCertRdmrInputs certRdmrAc
  (otherIns, otherMint, otherOuts) <- genOthers 5
  let certTokensToBurn = inv . fold $ [txOutValue certInOut | TxInInfo _ certInOut <- certIns]
      ins = certIns <> certRdmrIns <> otherIns
      mint = otherMint <> certTokensToBurn
      outs = otherOuts
      Interval _ (UpperBound upper _) = certValidity
      ctx = mkScriptContext (Minting certCs) ins [] mint outs []
  return $ setValidity ctx (interval' upper PosInf)

genCorruptCertMpBurningCtx :: CertMpParams -> CurrencySymbol -> AssetClass -> Gen ScriptContext
genCorruptCertMpBurningCtx certMpParams certCs certRdmrAc = do
  let certVAddr = cmp'certVAddress certMpParams

  ctx <- genCorrectCertMpBurningCtx certMpParams certCs certRdmrAc

  -- Randomly pick corruptions
  corruptions <-
    suchThat
      ( sublistOf
          [ doMintAndPayOtherTokenNameAddr certCs certVAddr
          , doRemoveInputsWithToken certRdmrAc
          , doValidityAlways
          , doValidityBefore
          ]
      )
      (not . null)

  let corrupt = mkCorrupt corruptions

  return $ corrupt ctx

genCorrectAuthMpMintingCtx :: AuthMpParams -> CurrencySymbol -> Gen ScriptContext
genCorrectAuthMpMintingCtx authMpParams authCs = do
  let aaAc = amp'authAuthorityAc authMpParams
      aaQ = amp'requiredAtLeastAaQ authMpParams
  aaIns <- genAaInputs aaAc aaQ
  addr <- genAddress
  (otherIns, otherMint, otherOuts) <- genOthers 5
  let ins = aaIns <> otherIns
      authId = toBuiltin . hashTxInputs $ aaIns
      authTn = TokenName authId
      authToken = assetClassValue (assetClass authCs authTn) 1
      authOut = TxOut addr authToken NoOutputDatum Nothing
      mint = otherMint <> authToken
      outs = otherOuts <> [authOut]
  return $
    mkScriptContext (Minting authCs) ins [] mint outs [] -- INFO: Unbalanced transaction

genCorruptAuthMpMintingCtx :: AuthMpParams -> CurrencySymbol -> Gen ScriptContext
genCorruptAuthMpMintingCtx authMpParams authCs = do
  ctx <- genCorrectAuthMpMintingCtx authMpParams authCs

  -- Randomly pick corruptions
  corruptions <-
    suchThat (sublistOf [doMintAndPayOtherTokenName authCs]) (not . null)

  let corrupt = mkCorrupt corruptions

  return $ corrupt ctx

genCorrectAuthMpBurningCtx :: CurrencySymbol -> Gen ScriptContext
genCorrectAuthMpBurningCtx authCs = do
  authIns <- genAuthInputs authCs
  (otherIns, otherMint, otherOuts) <- genOthers 5
  let ins = authIns <> otherIns
      authTokensToBurn = inv . fold $ [txOutValue authInOut | TxInInfo _ authInOut <- authIns]
      mint = otherMint <> authTokensToBurn
      outs = otherOuts
  return $ mkScriptContext (Minting authCs) ins [] mint outs []

genCorruptAuthMpBurningCtx :: CurrencySymbol -> Gen ScriptContext
genCorruptAuthMpBurningCtx authCs = do
  ctx <- genCorrectAuthMpBurningCtx authCs

  otherAddr <- genAddress

  -- Randomly pick corruptions
  corruptions <-
    suchThat (sublistOf [doMintAndPayOtherTokenNameAddr authCs otherAddr]) (not . null)

  let corrupt = mkCorrupt corruptions

  return $ corrupt ctx

genCorrectMustBurnOwnSingletonValueCtx :: Gen ScriptContext
genCorrectMustBurnOwnSingletonValueCtx = snd <$> genCorrectMustBurnOwnSingletonValueCtx'

genCorrectMustBurnOwnSingletonValueCtx' :: Gen ((TxOutRef, (CurrencySymbol, TokenName, Integer)), ScriptContext)
genCorrectMustBurnOwnSingletonValueCtx' = do
  spentIn <- genInput
  (otherIns, otherMint, otherOuts) <- genOthers 5
  let TxInInfo spentOref (TxOut _ spentVal _ _) = spentIn
      tokensToBurn = inv spentVal
      ins = otherIns <> [spentIn]
      mint = otherMint <> tokensToBurn
      outs = otherOuts
  return ((spentOref, head . flattenValue $ spentVal), mkScriptContext (Spending spentOref) ins [] mint outs [])

genCorruptMustBurnOwnSingletonValueCtx :: Gen ScriptContext
genCorruptMustBurnOwnSingletonValueCtx = do
  (_, ctx) <- genCorrectMustBurnOwnSingletonValueCtx'

  otherAddr <- genAddress
  -- Randomly pick corruptions
  corruptions <-
    suchThat (sublistOf [doPayInsteadOfBurn otherAddr]) (not . null)

  let corrupt = mkCorrupt corruptions

  return $ corrupt ctx

genCorrectCertVSpendingCtx :: CurrencySymbol -> Address -> Gen ScriptContext
genCorrectCertVSpendingCtx certCs certVAddr = do
  certRdmrAc <- genCertRdmrAc
  validity <- genValidity
  certIns <- genCertInputs certVAddr certCs certRdmrAc validity
  (otherIns, _, _) <- genOthers 5
  let tokensToBurn = inv . fold $ [txOutValue inOut | TxInInfo _ inOut <- ins]
      ins = certIns <> otherIns
  return $ mkScriptContext (Spending (txInInfoOutRef . head $ ins)) ins [] tokensToBurn [] []

genCorruptCertVSpendingCtx :: CurrencySymbol -> Address -> Gen ScriptContext
genCorruptCertVSpendingCtx certCs certVAddr = do
  ctx <- genCorrectCertVSpendingCtx certCs certVAddr

  otherAddr <- genAddress

  -- Randomly pick corruptions
  corruptions <-
    suchThat (sublistOf [doPayInsteadOfBurn otherAddr]) (not . null)

  let corrupt = mkCorrupt corruptions

  return $ corrupt ctx

genCorrectFsMpMintingCtx :: FsMpParams -> CurrencySymbol -> Gen ScriptContext
genCorrectFsMpMintingCtx fsMpParams fsCs = do
  let certCs = ap'certTokenCs . fmp'authParams $ fsMpParams
      authCs = ap'authTokenCs . fmp'authParams $ fsMpParams
      fsVAddr = fmp'fsVAddress fsMpParams
  certRdmrAc <- genCertRdmrAc
  certVAddr <- genAddress
  submitter <- genPubKeyHash
  nCerts <- chooseInt (1, 5)
  certIds <- replicateM nCerts genAuthenticatonId
  validity <- genValidity
  certRefs <- for certIds (genCertInput certVAddr certCs certRdmrAc validity)
  authIns <- for certIds (genAuthInput authCs)
  (otherIns, otherMint, otherOuts) <- genOthers 5
  let authsBurned = mconcat [Value.singleton authCs (TokenName certId) (-1) | certId <- certIds]
      fsVOuts =
        [ TxOut
            fsVAddr
            (Value.singleton fsCs (TokenName . toBuiltin $ hashTxInputs [authIn]) 1)
            (toOutputDatum $ FsDatum (toBuiltinData True) "deadbeef" (Finite 100) submitter)
            Nothing
        | authIn <- authIns
        ]
      fsMinted = mconcat [txOutValue fsVOut | fsVOut <- fsVOuts]
      ins = otherIns <> authIns
      mint = otherMint <> fsMinted <> authsBurned
      outs = otherOuts <> fsVOuts
      ctx = mkScriptContext (Minting fsCs) ins certRefs mint outs []
  return $ setValidity ctx validity

genCorruptFsMpMintingCtx :: FsMpParams -> CurrencySymbol -> Gen ScriptContext
genCorruptFsMpMintingCtx fsMpParams fsCs = do
  ctx <- genCorrectFsMpMintingCtx fsMpParams fsCs
  let certCs = ap'certTokenCs . fmp'authParams $ fsMpParams
      authCs = ap'authTokenCs . fmp'authParams $ fsMpParams
      fsVAddr = fmp'fsVAddress fsMpParams
  otherAddr <- genAddress

  -- Randomly pick corruptions
  corruptions <-
    suchThat
      ( sublistOf
          [ doPayInsteadOfBurn otherAddr
          , doMintAndPayOtherTokenNameAddr fsCs otherAddr
          , doMintAndPayOtherTokenNameAddr fsCs fsVAddr
          , doRemoveOutputDatum
          , doPayToOtherAddress fsVAddr otherAddr
          , doRemoveRefInputsWithCurrency certCs
          , doRemoveInputsWithCurrency authCs
          , doValidityAlways
          , doValidityBefore
          ]
      )
      (not . null)

  let corrupt = mkCorrupt corruptions
  return $ corrupt ctx

genCorrectFsMpBurningCtx :: FsMpParams -> CurrencySymbol -> Gen ScriptContext
genCorrectFsMpBurningCtx fsMpParams fsCs = do
  let fsVAddr = fmp'fsVAddress fsMpParams
  fsMintCtx <- genCorrectFsMpMintingCtx fsMpParams fsCs
  (otherIns, otherMint, otherOuts) <- genOthers 5

  let fsVOuts = [out | out <- txInfoOutputs . scriptContextTxInfo $ fsMintCtx, txOutAddress out == fsVAddr]

  fsIns <- for fsVOuts (\fsOut -> TxInInfo <$> genTxOutRef <*> pure fsOut)

  let fsDatums = [fsDat | out <- fsVOuts, OutputDatum (Datum dat) <- [txOutDatum out], fsDat <- maybe [] pure (fromBuiltinData @FsDatum dat)]
      gcAfter = maximum [fs'gcAfter fsDatum | fsDatum <- fsDatums]
      submitters = [fs'submitter fsDatum | fsDatum <- fsDatums]
      fsBurned = mconcat [inv $ txOutValue fsVOut | fsVOut <- fsVOuts]
      ins = otherIns <> fsIns
      mint = otherMint <> fsBurned
      outs = otherOuts
      ctx = mkScriptContext (Minting fsCs) ins [] mint outs submitters
  return $ setValidity ctx (interval' gcAfter PosInf)

genCorruptFsMpBurningCtx :: FsMpParams -> CurrencySymbol -> Gen ScriptContext
genCorruptFsMpBurningCtx fsMpParams fsCs = do
  ctx <- genCorrectFsMpBurningCtx fsMpParams fsCs
  let fsVAddr = fmp'fsVAddress fsMpParams
  otherAddr <- genAddress

  -- Randomly pick corruptions
  corruptions <-
    suchThat
      ( sublistOf
          [ doPayInsteadOfBurn otherAddr
          , doPayInsteadOfBurn fsVAddr
          , doMintAndPayOtherTokenNameAddr fsCs otherAddr
          , doMintAndPayOtherTokenNameAddr fsCs fsVAddr
          , doValidityAlways
          , doValidityBefore
          ]
      )
      (not . null)

  let corrupt = mkCorrupt corruptions

  return $ corrupt ctx

genCorrectFsVSpendingCtx :: Gen ScriptContext
genCorrectFsVSpendingCtx = do
  spendingIn <- genInput
  someIns <- replicateM 10 genInput
  (otherIns, otherMint, otherOuts) <- genOthers 5

  let tokensToBurn = inv . fold $ [txOutValue inOut | TxInInfo _ inOut <- ins]
      ins = otherIns <> someIns <> [spendingIn]
      mint = otherMint <> tokensToBurn
      outs = otherOuts
  return $ mkScriptContext (Spending (txInInfoOutRef spendingIn)) ins [] mint outs []

genCorruptFsVSpendingCtx :: Gen ScriptContext
genCorruptFsVSpendingCtx = do
  ctx <- genCorrectFsVSpendingCtx

  otherAddr <- genAddress

  -- Randomly pick corruptions
  corruptions <-
    suchThat (sublistOf [doPayInsteadOfBurn otherAddr]) (not . null)

  let corrupt = mkCorrupt corruptions

  return $ corrupt ctx

genFsRefInput :: CurrencySymbol -> FactStatement -> Gen TxInInfo
genFsRefInput fsCs fs = do
  addr <- genAddress
  fsTn <- genTokenName
  fsId <- genBuiltinByteString "fsid" 5
  submitter <- genPubKeyHash
  return $
    TxInInfo
      (TxOutRef (TxId fsId) 0)
      ( TxOut
          addr
          (Value.singleton fsCs fsTn 1)
          (toOutputDatum $ FsDatum fs (LedgerBytes fsId) PosInf submitter)
          Nothing
      )

genCorrectConsumerCtx :: CurrencySymbol -> FactStatement -> Gen ScriptContext
genCorrectConsumerCtx fsCs fs = do
  spendingIn <- genInput
  fsRefIn <- genFsRefInput fsCs fs

  return $ mkScriptContext (Spending (txInInfoOutRef spendingIn)) [spendingIn] [fsRefIn] mempty [] []

genInput :: Gen TxInInfo
genInput = (\outRef val addr -> TxInInfo outRef (TxOut addr val NoOutputDatum Nothing)) <$> genTxOutRef <*> genSingletonValue <*> genAddress

genInputs :: Int -> Gen [TxInInfo]
genInputs n = replicateM n genInput

genSingletonValue :: Gen Value
genSingletonValue = do
  v <- Value.singleton <$> genCurrencySymbol <*> genTokenName <*> chooseInteger (1, 100)
  pure $ lovelaceValue 1 <> v

genOthers :: Int -> Gen ([TxInInfo], Value, [TxOut])
genOthers n = do
  ins <- genInputs n
  outAddrs <- replicateM n genAddress
  let inVals = mconcat [flattenValue v | TxInInfo _ (TxOut _ v _ _) <- ins]
  mints <- mconcat . (flattenValue <$>) <$> replicateM n genSingletonValue
  inToOutVals <- sublistOf inVals
  let outVals = mints <> inToOutVals
      burnVals = Set.toList $ Set.difference (Set.fromList inVals) (Set.fromList inToOutVals)
  outAddrsWithVals <- distribute outVals (Set.fromList outAddrs)
  let outs = [TxOut addr (valueFromList vals) NoOutputDatum Nothing | (addr, vals) <- Map.toList outAddrsWithVals]
      minted = valueFromList mints <> inv (valueFromList burnVals)
  return (ins, minted, outs)

valueFromList :: [(CurrencySymbol, TokenName, Integer)] -> Value
valueFromList vals = mconcat [Value.singleton c t q | (c, t, q) <- vals]

genBuiltinByteString :: String -> Int -> Gen BuiltinByteString
genBuiltinByteString prefix len = do
  suffix <- vectorOf len (chooseEnum ('a', 'z'))
  return . stringToBuiltinByteString . take len $ prefix <> suffix

genTxOutRef :: Gen TxOutRef
genTxOutRef = do
  txId <- genBuiltinByteString "txid-" 28
  txIx <- chooseInteger (0, 255)
  return $ TxOutRef (TxId txId) txIx

genAddress :: Gen Address
genAddress = do
  scriptOrWallet :: Bool <- arbitrary
  if scriptOrWallet
    then do
      bs <- genBuiltinByteString "vh-" 28
      return . scriptHashAddress . ScriptHash $ bs
    else pubKeyHashAddress <$> genPubKeyHash

genPubKeyHash :: Gen PubKeyHash
genPubKeyHash = do
  bs <- genBuiltinByteString "pkh-" 28
  return . PubKeyHash $ bs

genTokenName :: Gen TokenName
genTokenName = TokenName <$> genBuiltinByteString "tn-" 32

genCurrencySymbol :: Gen CurrencySymbol
genCurrencySymbol = CurrencySymbol <$> genBuiltinByteString "cs-" 28

genAuthenticatonId :: Gen BuiltinByteString
genAuthenticatonId = genBuiltinByteString "authid-" 28

-- | Distributes values (first argument) over the keys (second) to create a random Map
distribute :: Ord a => [b] -> Set a -> Gen (Map a [b])
distribute total xs = do
  (leftover, distributed) <- distributeSingle total xs
  if null leftover
    then return distributed
    else do
      distributed' <- distribute leftover xs
      return $ Map.unionWith (<>) distributed distributed'

distributeSingle :: Ord a => [b] -> Set a -> Gen ([b], Map a [b])
distributeSingle total =
  foldM
    ( \(budget, dist) x ->
        if null budget
          then return (budget, Map.insert x [] dist)
          else do
            (taken, budget') <- take' budget []
            return (budget', Map.insert x taken dist)
    )
    (total, mempty)
  where
    take' [] outs = return (outs, [])
    take' (i : ins) outs = do
      b <- chooseAny
      if b
        then take' ins (i : outs)
        else return (outs, i : ins)

{-| Mutating functions to introduce corruptions into ScriptContext

TODO: Use mlabs-haskell/plutus-simple-model to ensure ledger invariances for the mutated ScriptContexts
WARN: All these mutations are untested and fairly unreliable -}
-- | Makes a ScriptContext corruption pipeline
mkCorrupt :: [ScriptContext -> ScriptContext] -> ScriptContext -> ScriptContext
mkCorrupt = foldr (.) id

-- | Mints a token with a specified CurrencySymbol and 'other token name' and pays it to same output
doMintAndPayOtherTokenName :: CurrencySymbol -> ScriptContext -> ScriptContext
doMintAndPayOtherTokenName cs ctx =
  let ScriptContext txInfo _ = ctx
      otherAc = assetClass cs (TokenName "other token name")
   in ctx
        { scriptContextTxInfo =
            txInfo
              { txInfoMint = txInfoMint txInfo <> assetClassValue otherAc (toInteger . length . txInfoOutputs $ txInfo)
              , txInfoOutputs = txInfoOutputs txInfo <> [out {txOutValue = assetClassValue otherAc 1 <> txOutValue out} | out <- txInfoOutputs txInfo]
              }
        }

-- | Mints a token with a specified CurrencySymbol and 'other token name' and pays it a specified address
doMintAndPayOtherTokenNameAddr :: CurrencySymbol -> Address -> ScriptContext -> ScriptContext
doMintAndPayOtherTokenNameAddr cs addr ctx =
  let ScriptContext txInfo _ = ctx
      otherAc = assetClass cs (TokenName "other token name")
   in ctx
        { scriptContextTxInfo =
            txInfo
              { txInfoMint = txInfoMint txInfo <> assetClassValue otherAc 1
              , txInfoOutputs = txInfoOutputs txInfo <> [TxOut addr (assetClassValue otherAc 1) NoOutputDatum Nothing]
              }
        }

-- | Removes datums from all outputs
doRemoveOutputDatum :: ScriptContext -> ScriptContext
doRemoveOutputDatum ctx =
  let ScriptContext txInfo _ = ctx
   in ctx
        { scriptContextTxInfo =
            txInfo
              { txInfoOutputs = [out {txOutDatum = NoOutputDatum} | out <- txInfoOutputs txInfo]
              }
        }

-- | Replaces original address with some other address
doPayToOtherAddress :: Address -> Address -> ScriptContext -> ScriptContext
doPayToOtherAddress originalAddr otherAddr ctx =
  let ScriptContext txInfo _ = ctx
   in ctx
        { scriptContextTxInfo =
            txInfo
              { txInfoOutputs = [out {txOutAddress = otherAddr} | out <- txInfoOutputs txInfo, txOutAddress out == originalAddr]
              }
        }

-- | Removes inputs that contain a specified AssetClass
doRemoveInputsWithToken :: AssetClass -> ScriptContext -> ScriptContext
doRemoveInputsWithToken ac ctx =
  let ScriptContext txInfo _ = ctx
   in ctx
        { scriptContextTxInfo =
            txInfo
              { txInfoInputs = [inp | inp@(TxInInfo _ inOut) <- txInfoInputs txInfo, assetClassValueOf (txOutValue inOut) ac > 0]
              }
        }

-- | Removes ref inputs that contain a specified CurrencySymbol
doRemoveRefInputsWithCurrency :: CurrencySymbol -> ScriptContext -> ScriptContext
doRemoveRefInputsWithCurrency cs ctx =
  let ScriptContext txInfo _ = ctx
   in ctx
        { scriptContextTxInfo =
            txInfo
              { txInfoReferenceInputs = [inp | inp@(TxInInfo _ inOut) <- txInfoReferenceInputs txInfo, not . AssocMap.member cs $ getValue (txOutValue inOut)]
              }
        }

-- | Removes inputs that contain a specified CurrencySymbol
doRemoveInputsWithCurrency :: CurrencySymbol -> ScriptContext -> ScriptContext
doRemoveInputsWithCurrency cs ctx =
  let ScriptContext txInfo _ = ctx
   in ctx
        { scriptContextTxInfo =
            txInfo
              { txInfoInputs = [inp | inp@(TxInInfo _ inOut) <- txInfoInputs txInfo, not . AssocMap.member cs $ getValue (txOutValue inOut)]
              }
        }

-- | Removes burned tokens and pais them out to a specified address
doPayInsteadOfBurn :: Address -> ScriptContext -> ScriptContext
doPayInsteadOfBurn addr ctx =
  let ScriptContext txInfo _ = ctx
      burnedVal = mconcat [Value.singleton cs tn q | (cs, tn, q) <- flattenValue . txInfoMint $ txInfo, q < 0]
      mintedVal = mconcat [Value.singleton cs tn q | (cs, tn, q) <- flattenValue . txInfoMint $ txInfo, q > 0]
   in ctx
        { scriptContextTxInfo =
            txInfo
              { txInfoMint = mintedVal
              , txInfoOutputs = txInfoOutputs txInfo <> [TxOut addr (inv burnedVal) NoOutputDatum Nothing]
              }
        }

doValidityBefore :: ScriptContext -> ScriptContext
doValidityBefore ctx =
  let ScriptContext txInfo _ = ctx
      Interval (LowerBound l _) _ = txInfoValidRange . scriptContextTxInfo $ ctx
   in ctx
        { scriptContextTxInfo =
            txInfo
              { txInfoValidRange = interval' NegInf l
              }
        }

doValidityAlways :: ScriptContext -> ScriptContext
doValidityAlways ctx =
  let ScriptContext txInfo _ = ctx
   in ctx
        { scriptContextTxInfo =
            txInfo
              { txInfoValidRange = interval' NegInf PosInf
              }
        }

-- | For debugging
_doNothing :: ScriptContext -> ScriptContext
_doNothing = id

-- TODO: Switch to mlabs-haskell/plutus-simple-model (that's why you need it)
normalizeValue :: Value -> Value
normalizeValue v =
  Value . AssocMap.safeFromList . Map.toList . (AssocMap.safeFromList . Map.toList <$>) $
    Map.unionsWith
      (Map.unionWith (+))
      ( [ Map.singleton cs (Map.singleton tn q)
        | (cs, tokens) <- AssocMap.toList . getValue $ v
        , (tn, q) <- AssocMap.toList tokens
        ]
      )

-- | Creates an interval with Extended bounds
interval' :: forall a. Extended a -> Extended a -> Interval a
interval' from' to' = Interval (LowerBound from' False) (UpperBound to' False)

hashTxInputs :: [TxInInfo] -> ByteString
hashTxInputs inputs =
  let
    orefs = [oref | TxInInfo oref _ <- inputs]
    sortedOrefs = sort orefs
    ixs = fmap (fromInteger . Value.txOutRefIdx) sortedOrefs
    txIds = fmap (Value.fromBuiltin . Value.getTxId . Value.txOutRefId) sortedOrefs
    hashedOref = convert @_ @ByteString . hashWith Blake2b_256 . mconcat $ zipWith cons ixs txIds
   in
    hashedOref
