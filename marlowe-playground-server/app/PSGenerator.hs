{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

module PSGenerator
    ( generate
    ) where

import qualified API
import qualified Auth
import qualified ContractForDifference
import           Control.Applicative                              ((<|>))
import           Control.Lens                                     (set, (&))
import           Control.Monad.Reader                             (MonadReader)
import           Data.Aeson                                       (encode)
import qualified Data.ByteString                                  as BS
import qualified Data.ByteString.Char8                            as BS8
import qualified Data.ByteString.Lazy.Char8                       as Char8
import           Data.Monoid                                      ()
import           Data.Proxy                                       (Proxy (Proxy))
import qualified Data.Set                                         as Set ()
import qualified Data.Text.Encoding                               as T ()
import qualified Data.Text.IO                                     as T ()
import qualified Escrow
import qualified Example
import           Language.Haskell.Interpreter                     (CompilationError, InterpreterError,
                                                                   InterpreterResult, SourceCode, Warning)
import           Language.Marlowe
import qualified Language.Marlowe.ACTUS.Definitions.ContractTerms as CT
import qualified Language.PlutusTx.AssocMap                       as Map
import           Language.PureScript.Bridge                       (BridgePart, Language (Haskell), PSType, SumType,
                                                                   TypeInfo (TypeInfo), buildBridge, genericShow,
                                                                   mkSumType, psTypeParameters, typeModule, typeName,
                                                                   writePSTypesWith, (^==))
import           Language.PureScript.Bridge.Builder               (BridgeData)
import           Language.PureScript.Bridge.CodeGenSwitches       (ForeignOptions (ForeignOptions), defaultSwitch,
                                                                   genForeign)
import           Language.PureScript.Bridge.PSTypes               (psNumber, psString)
import           Language.PureScript.Bridge.TypeParameters        (A)
import           Marlowe.Contracts                                (contractForDifference, couponBondGuaranteed, escrow,
                                                                   example, swap, zeroCouponBond)
import qualified Marlowe.Symbolic.Server                          as MS
import qualified Marlowe.Symbolic.Types.Request                   as MSReq
import qualified Marlowe.Symbolic.Types.Response                  as MSRes
import qualified Option
import qualified PSGenerator.Common
import           Servant                                          ((:<|>), (:>))
import           Servant.PureScript                               (HasBridge, Settings, apiModuleName, defaultBridge,
                                                                   defaultSettings, languageBridge,
                                                                   writeAPIModuleWithSettings, _generateSubscriberAPI)
import qualified Swap
import           System.Directory                                 (createDirectoryIfMissing)
import           System.FilePath                                  ((</>))
import qualified Webghc.Server                                    as Webghc
import qualified ZeroCouponBond


psContract :: MonadReader BridgeData m => m PSType
psContract =
    TypeInfo "marlowe-playground-client" "Marlowe.Semantics" "Contract" <$>
    psTypeParameters

contractBridge :: BridgePart
contractBridge = do
    typeName ^== "Contract"
    typeModule ^== "Language.Marlowe.Semantics"
    psContract

psState :: MonadReader BridgeData m => m PSType
psState =
    TypeInfo "marlowe-playground-client" "Marlowe.Semantics" "State" <$>
    psTypeParameters

stateBridge :: BridgePart
stateBridge = do
    typeName ^== "State"
    typeModule ^== "Language.Marlowe.Semantics"
    psState

psTransactionInput :: MonadReader BridgeData m => m PSType
psTransactionInput =
    TypeInfo "marlowe-playground-client" "Marlowe.Semantics" "TransactionInput" <$>
    psTypeParameters

transactionInputBridge :: BridgePart
transactionInputBridge = do
    typeName ^== "TransactionInput"
    typeModule ^== "Language.Marlowe.Semantics"
    psTransactionInput

psTransactionWarning :: MonadReader BridgeData m => m PSType
psTransactionWarning =
    TypeInfo "marlowe-playground-client" "Marlowe.Semantics" "TransactionWarning" <$>
    psTypeParameters

transactionWarningBridge :: BridgePart
transactionWarningBridge = do
    typeName ^== "TransactionWarning"
    typeModule ^== "Language.Marlowe.Semantics"
    psTransactionWarning

doubleBridge :: BridgePart
doubleBridge = typeName ^== "Double" >> return psNumber

dayBridge :: BridgePart
dayBridge = typeName ^== "Day" >> return psString

myBridge :: BridgePart
myBridge =
    PSGenerator.Common.aesonBridge <|> PSGenerator.Common.containersBridge <|>
    PSGenerator.Common.languageBridge <|>
    PSGenerator.Common.ledgerBridge <|>
    PSGenerator.Common.servantBridge <|>
    PSGenerator.Common.miscBridge <|>
    doubleBridge <|>
    dayBridge <|>
    contractBridge <|>
    stateBridge <|>
    transactionInputBridge <|>
    transactionWarningBridge <|>
    defaultBridge

data MyBridge

myBridgeProxy :: Proxy MyBridge
myBridgeProxy = Proxy

instance HasBridge MyBridge where
    languageBridge _ = buildBridge myBridge

myTypes :: [SumType 'Haskell]
myTypes =
    PSGenerator.Common.ledgerTypes <>
    PSGenerator.Common.walletTypes <>
    PSGenerator.Common.playgroundTypes <>
    [ mkSumType (Proxy @SourceCode)
    , mkSumType (Proxy @CompilationError)
    , mkSumType (Proxy @InterpreterError)
    , mkSumType (Proxy @Warning)
    , mkSumType (Proxy @(InterpreterResult A))
    , (genericShow <*> mkSumType) (Proxy @MSRes.Result)
    , mkSumType (Proxy @MSReq.Request)
    , mkSumType (Proxy @CT.ContractTerms)
    , mkSumType (Proxy @CT.PYTP)
    , mkSumType (Proxy @CT.PREF)
    , mkSumType (Proxy @CT.SCEF)
    , mkSumType (Proxy @CT.Cycle)
    , mkSumType (Proxy @CT.Period)
    , mkSumType (Proxy @CT.Stub)
    , mkSumType (Proxy @CT.ScheduleConfig)
    , mkSumType (Proxy @CT.DCC)
    , mkSumType (Proxy @CT.BDC)
    , mkSumType (Proxy @CT.EOMC)
    , mkSumType (Proxy @CT.ContractStatus)
    , mkSumType (Proxy @CT.FEB)
    , mkSumType (Proxy @CT.IPCB)
    , mkSumType (Proxy @CT.ContractRole)
    , mkSumType (Proxy @CT.ContractType)
    , mkSumType (Proxy @CT.Assertion)
    , mkSumType (Proxy @CT.Assertions)
    , mkSumType (Proxy @CT.AssertionContext)
    , mkSumType (Proxy @Webghc.CompileRequest)
    ]

mySettings :: Settings
mySettings =
    (defaultSettings & set apiModuleName "Marlowe")
        {_generateSubscriberAPI = False}

multilineString :: BS.ByteString -> BS.ByteString -> BS.ByteString
multilineString name value =
    "\n\n" <> name <> " :: String\n" <> name <> " = \"\"\"" <> value <> "\"\"\""

psModule :: BS.ByteString -> BS.ByteString -> BS.ByteString
psModule name body = "module " <> name <> " where" <> body

writeUsecases :: FilePath -> IO ()
writeUsecases outputDir = do
    let haskellUsecases =
            multilineString "example" example
         <> multilineString "escrow" escrow
         <> multilineString "zeroCouponBond" zeroCouponBond
         <> multilineString "couponBondGuaranteed" couponBondGuaranteed
         <> multilineString "swap" swap
         <> multilineString "contractForDifference" contractForDifference
        haskellUsecasesModule = psModule "Examples.Haskell.Contracts" haskellUsecases
    createDirectoryIfMissing True (outputDir </> "Examples" </> "Haskell")
    BS.writeFile (outputDir </> "Examples" </> "Haskell" </> "Contracts.purs") haskellUsecasesModule
    let contractToString = BS8.pack . show . pretty
        marloweUsecases =
            multilineString "example" (contractToString Example.contract)
         <> multilineString "escrow" (contractToString Escrow.contract)
         <> multilineString "zeroCouponBond" (contractToString ZeroCouponBond.contract)
         <> multilineString "option" (contractToString Option.contract)
         <> multilineString "swap" (contractToString Swap.contract)
         <> multilineString "contractForDifference" (contractToString ContractForDifference.contract)
        marloweUsecasesModule = psModule "Examples.Marlowe.Contracts" marloweUsecases
    createDirectoryIfMissing True (outputDir </> "Examples" </> "Marlowe")
    BS.writeFile (outputDir </> "Examples" </> "Marlowe" </> "Contracts.purs") marloweUsecasesModule
    putStrLn outputDir

writePangramJson :: FilePath -> IO ()
writePangramJson outputDir = do

    let

        alicePk = PK "4ecde0775d081e45f06141416cbc3afed4c44a08c93ea31281e25c8fa03548b9"

        bobRole = Role "Bob"

        const100 = Constant 100

        choiceId = ChoiceId "choice" alicePk

        valueExpr = AddValue const100 (SubValue const100 (NegValue const100))

        token = Token "aa" "name"

    let pangram =
            Assert TrueObs
                (When
                    [ Case (Deposit alicePk alicePk ada valueExpr)
                        ( Let (ValueId "x") valueExpr
                            (Pay alicePk (Party bobRole) ada (Cond TrueObs (UseValue (ValueId "x")) (UseValue (ValueId "y"))) Close)
                        )
                    , Case (Choice choiceId [ Bound 0 1 ])
                        ( If (ChoseSomething choiceId `OrObs` (ChoiceValue choiceId `ValueEQ` Scale (1 % 10) const100))
                            (Pay alicePk (Account alicePk) token (AvailableMoney alicePk token) Close)
                            Close
                        )
                    , Case (Notify (AndObs (SlotIntervalStart `ValueLT` SlotIntervalEnd) TrueObs)) Close
                    ]
                    (Slot 100)
                    Close
                )
        encodedPangram = BS8.pack . Char8.unpack $ encode pangram
        state =
            State
            { accounts = Map.singleton (alicePk, token) 12
            , choices = Map.singleton choiceId 42
            , boundValues = Map.fromList [ ((ValueId "x"), 1), ((ValueId "y"), 2) ]
            , minSlot = Slot 123
            }
        encodedState = BS8.pack . Char8.unpack $ encode state
    createDirectoryIfMissing True (outputDir </> "JSON")
    BS.writeFile (outputDir </> "JSON" </> "contract.json") encodedPangram
    BS.writeFile (outputDir </> "JSON" </> "state.json") encodedState

type Web = ("api" :> (API.API :<|> Auth.FrontendAPI)) :<|> MS.API :<|> Webghc.FrontendAPI

generate :: FilePath -> IO ()
generate outputDir = do
    writeAPIModuleWithSettings
        mySettings
        outputDir
        myBridgeProxy
        (Proxy @Web)
    writePSTypesWith (defaultSwitch <> genForeign (ForeignOptions True)) outputDir (buildBridge myBridge) myTypes
    writeUsecases outputDir
    writePangramJson outputDir
