{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module PSGenerator.Common where

import           Auth                                      (AuthRole, AuthStatus)
import           Control.Applicative                       (empty, (<|>))
import           Control.Monad.Reader                      (MonadReader)
import           Data.Proxy                                (Proxy (Proxy))
import           Gist                                      (Gist, GistFile, GistId, NewGist, NewGistFile, Owner)
import           Language.Plutus.Contract.Checkpoint       (CheckpointError)
import           Language.PureScript.Bridge                (BridgePart, Language (Haskell), PSType, SumType,
                                                            TypeInfo (TypeInfo), doCheck, equal, equal1, functor,
                                                            genericShow, haskType, isTuple, mkSumType, order,
                                                            psTypeParameters, typeModule, typeName, (^==))
import           Language.PureScript.Bridge.Builder        (BridgeData)
import           Language.PureScript.Bridge.PSTypes        (psArray, psInt, psNumber, psString)
import           Language.PureScript.Bridge.TypeParameters (A)
import           Ledger                                    (Address, Datum, DatumHash, MonetaryPolicy, PubKey,
                                                            PubKeyHash, Redeemer, Signature, Tx, TxId, TxIn, TxInType,
                                                            TxOut, TxOutRef, TxOutTx, TxOutType, UtxoIndex, Validator)
import           Ledger.Ada                                (Ada)
import           Ledger.Constraints.OffChain               (MkTxError)
import           Ledger.Index                              (ValidationError)
import           Ledger.Interval                           (Extended, Interval, LowerBound, UpperBound)
import           Ledger.Scripts                            (ScriptError)
import           Ledger.Slot                               (Slot)
import           Ledger.Typed.Tx                           (ConnectionError)
import           Ledger.Value                              (CurrencySymbol, TokenName, Value)
import           Playground.Types                          (ContractCall, FunctionSchema, KnownCurrency)
import           Schema                                    (FormArgumentF, FormSchema)
import           Wallet.API                                (WalletAPIError)
import qualified Wallet.Emulator.Wallet                    as EM
import           Wallet.Rollup.Types                       (AnnotatedTx, BeneficialOwner, DereferencedInput, SequenceId,
                                                            TxKey)
import           Wallet.Types                              (AssertionError, ContractError, ContractInstanceId,
                                                            EndpointDescription, MatchingError, Notification,
                                                            NotificationError)

psJson :: PSType
psJson = TypeInfo "web-common" "Data.RawJson" "RawJson" []

psNonEmpty :: MonadReader BridgeData m => m PSType
psNonEmpty =
    TypeInfo "web-common" "Data.Json.JsonNonEmptyList" "JsonNonEmptyList" <$>
    psTypeParameters

psMap :: MonadReader BridgeData m => m PSType
psMap = TypeInfo "purescript-ordered-collections" "Data.Map" "Map" <$> psTypeParameters

psUnit :: PSType
psUnit = TypeInfo "web-common" "Data.Unit" "Unit" []

-- Note: Haskell has multi-section Tuples, whereas PureScript just uses nested pairs.
psJsonTuple :: MonadReader BridgeData m => m PSType
psJsonTuple = expand <$> psTypeParameters
  where
    expand []       = psUnit
    expand [x]      = x
    expand p@[_, _] = TypeInfo "web-common" "Data.Json.JsonTuple" "JsonTuple" p
    expand (x:ys)   = TypeInfo "web-common" "Data.Json.JsonTuple" "JsonTuple" [x, expand ys]

psJsonUUID :: PSType
psJsonUUID = TypeInfo "web-common" "Data.Json.JsonUUID" "JsonUUID" []

uuidBridge :: BridgePart
uuidBridge = do
    typeName ^== "UUID"
    typeModule ^== "Data.UUID" <|> typeModule ^== "Data.UUID.Types.Internal"
    pure psJsonUUID

mapBridge :: BridgePart
mapBridge = do
    typeName ^== "Map"
    typeModule ^== "Data.Map.Internal"
    psMap

aesonValueBridge :: BridgePart
aesonValueBridge = do
    typeName ^== "Value"
    typeModule ^== "Data.Aeson.Types.Internal"
    pure psJson

tupleBridge :: BridgePart
tupleBridge = do
    doCheck haskType isTuple
    psJsonTuple

aesonBridge :: BridgePart
aesonBridge =
    mapBridge <|> tupleBridge <|> aesonValueBridge <|> uuidBridge

------------------------------------------------------------
setBridge :: BridgePart
setBridge = do
    typeName ^== "Set"
    typeModule ^== "Data.Set" <|> typeModule ^== "Data.Set.Internal"
    psArray

nonEmptyBridge :: BridgePart
nonEmptyBridge = do
    typeName ^== "NonEmpty"
    typeModule ^== "GHC.Base"
    psNonEmpty

containersBridge :: BridgePart
containersBridge = nonEmptyBridge <|> setBridge

------------------------------------------------------------
integerBridge :: BridgePart
integerBridge = do
    typeName ^== "Integer"
    pure psBigInteger

digestBridge :: BridgePart
digestBridge = do
    typeName ^== "Digest"
    typeModule ^== "Crypto.Hash.Types"
    pure psString

byteStringBridge :: BridgePart
byteStringBridge = do
    typeName ^== "ByteString"
    typeModule ^== "Data.ByteString.Lazy.Internal" <|> typeModule ^== "Data.ByteString.Internal"
    pure psString

scientificBridge :: BridgePart
scientificBridge = do
    typeName ^== "Scientific"
    typeModule ^== "Data.Scientific"
    pure psNumber


naturalBridge :: BridgePart
naturalBridge = do
    typeName ^== "Natural"
    typeModule ^== "GHC.Natural"
    pure psInt

miscBridge :: BridgePart
miscBridge =
    byteStringBridge <|> integerBridge <|> scientificBridge <|> digestBridge <|> naturalBridge

------------------------------------------------------------

psBigInteger :: PSType
psBigInteger = TypeInfo "purescript-foreign-generic" "Data.BigInteger" "BigInteger" []

psAssocMap :: MonadReader BridgeData m => m PSType
psAssocMap =
    TypeInfo "plutus-playground-client" "Language.PlutusTx.AssocMap" "Map" <$>
    psTypeParameters

dataBridge :: BridgePart
dataBridge = do
    typeName ^== "Data"
    typeModule ^== "Language.PlutusTx.Data"
    pure psString

assocMapBridge :: BridgePart
assocMapBridge = do
    typeName ^== "Map"
    typeModule ^== "Language.PlutusTx.AssocMap"
    psAssocMap

languageBridge :: BridgePart
languageBridge = dataBridge <|> assocMapBridge

------------------------------------------------------------
scriptBridge :: BridgePart
scriptBridge = do
    typeName ^== "Script"
    typeModule ^== "Ledger.Scripts"
    pure psString

validatorHashBridge :: BridgePart
validatorHashBridge = do
    typeName ^== "ValidatorHash"
    typeModule ^== "Ledger.Scripts"
    pure psString

mpsHashBridge :: BridgePart
mpsHashBridge = do
    typeName ^== "MonetaryPolicyHash"
    typeModule ^== "Ledger.Scripts"
    pure psString

ledgerBytesBridge :: BridgePart
ledgerBytesBridge = do
    typeName ^== "LedgerBytes"
    typeModule ^== "LedgerBytes"
    pure psString

ledgerBridge :: BridgePart
ledgerBridge =
    scriptBridge <|> validatorHashBridge <|> mpsHashBridge <|> ledgerBytesBridge

------------------------------------------------------------
headersBridge :: BridgePart
headersBridge = do
    typeModule ^== "Servant.API.ResponseHeaders"
    typeName ^== "Headers"
    -- Headers should have two parameters, the list of headers and the return type.
    psTypeParameters >>= \case
        [_, returnType] -> pure returnType
        _               -> empty

headerBridge :: BridgePart
headerBridge = do
    typeModule ^== "Servant.API.Header"
    typeName ^== "Header'"
    empty

servantBridge :: BridgePart
servantBridge = headersBridge <|> headerBridge

------------------------------------------------------------
ledgerTypes :: [SumType 'Haskell]
ledgerTypes =
    [ (equal <*> (genericShow <*> mkSumType)) (Proxy @Slot)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @Ada)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @Tx)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @TxId)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @TxIn)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @TxOut)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @TxOutTx)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @TxOutRef)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @UtxoIndex)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @Value)
    , (functor <*> (equal <*> (genericShow <*> mkSumType)))
          (Proxy @(Extended A))
    , (functor <*> (equal <*> (genericShow <*> mkSumType)))
          (Proxy @(Interval A))
    , (functor <*> (equal <*> (genericShow <*> mkSumType)))
          (Proxy @(LowerBound A))
    , (functor <*> (equal <*> (genericShow <*> mkSumType)))
          (Proxy @(UpperBound A))
    , (genericShow <*> (order <*> mkSumType)) (Proxy @CurrencySymbol)
    , (genericShow <*> (order <*> mkSumType)) (Proxy @MonetaryPolicy)
    , (genericShow <*> (order <*> mkSumType)) (Proxy @Redeemer)
    , (genericShow <*> (order <*> mkSumType)) (Proxy @Signature)
    , (genericShow <*> (order <*> mkSumType)) (Proxy @TokenName)
    , (genericShow <*> (order <*> mkSumType)) (Proxy @TxInType)
    , (genericShow <*> (order <*> mkSumType)) (Proxy @Validator)
    , (genericShow <*> mkSumType) (Proxy @ScriptError)
    , (genericShow <*> mkSumType) (Proxy @ValidationError)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @Address)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @Datum)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @DatumHash)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @PubKey)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @PubKeyHash)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @TxOutType)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @MkTxError)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @ContractError)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @ConnectionError)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @Notification)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @NotificationError)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @MatchingError)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @AssertionError)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @CheckpointError)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @ContractInstanceId)
    ]

walletTypes :: [SumType 'Haskell]
walletTypes =
    [ (equal <*> (genericShow <*> mkSumType)) (Proxy @AnnotatedTx)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @DereferencedInput)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @EM.Wallet)
    , (equal <*> (genericShow <*> mkSumType)) (Proxy @WalletAPIError)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @BeneficialOwner)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @SequenceId)
    , (order <*> (genericShow <*> mkSumType)) (Proxy @TxKey)
    ]

------------------------------------------------------------
playgroundTypes :: [SumType 'Haskell]
playgroundTypes =
    [ (genericShow <*> (equal <*> mkSumType)) (Proxy @FormSchema)
    , (functor <*> (genericShow <*> (equal <*> mkSumType)))
          (Proxy @(FunctionSchema A))
    , (functor <*> (equal <*> (equal1 <*> (genericShow <*> mkSumType))))
          (Proxy @(FormArgumentF A))
    , (genericShow <*> (order <*> mkSumType)) (Proxy @EndpointDescription)
    , (genericShow <*> (equal <*> mkSumType)) (Proxy @KnownCurrency)
    , (genericShow <*> (equal <*> mkSumType)) (Proxy @(ContractCall A))
    ] <>
    [ (order <*> mkSumType) (Proxy @GistId)
    , mkSumType (Proxy @Gist)
    , mkSumType (Proxy @GistFile)
    , mkSumType (Proxy @NewGist)
    , mkSumType (Proxy @NewGistFile)
    , mkSumType (Proxy @Owner)
    , mkSumType (Proxy @AuthStatus)
    , mkSumType (Proxy @AuthRole)
    ]
