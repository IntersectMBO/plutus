{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}
-- | Defines a number of types that are used in Wallet.XXX modules
module Wallet.Types(
    ContractInstanceId(..)
    , contractInstanceIDs
    , randomID
    , Notification(..)
    , EndpointDescription(..)
    , EndpointValue(..)
    , Payment(..)
    , emptyPayment
    , AddressChangeRequest(..)
    , AddressChangeResponse(..)
    -- * Error types
    , MatchingError(..)
    , AsMatchingError(..)
    , AssertionError(..)
    , AsAssertionError(..)
    , ContractError(..)
    , AsContractError(..)
    , NotificationError(..)
    , AsNotificationError(..)
    ) where

import           Control.Lens                        (prism')
import           Control.Lens.TH                     (makeClassyPrisms)
import           Data.Aeson                          (FromJSON, FromJSONKey, ToJSON, ToJSONKey)
import qualified Data.Aeson                          as Aeson
import qualified Data.Aeson.Encode.Pretty            as JSON
import qualified Data.ByteString.Lazy.Char8          as BSL8
import qualified Data.Set                            as Set
import           Data.String                         (IsString (..))
import           Data.Text                           (Text)
import qualified Data.Text                           as T
import           Data.Text.Prettyprint.Doc           (Pretty (..), colon, hang, viaShow, vsep, (<+>))
import           Data.Text.Prettyprint.Doc.Extras    (PrettyShow (..), Tagged (..))
import           Data.UUID                           (UUID)
import qualified Data.UUID.Extras                    as UUID
import qualified Data.UUID.V4                        as UUID
import           GHC.Generics                        (Generic)
import qualified Language.Haskell.TH.Syntax          as TH

import           Language.Plutus.Contract.Checkpoint (AsCheckpointError (..), CheckpointError)
import           Ledger                              (Address, Slot, Tx, TxIn, TxOut, txId)
import           Ledger.Constraints.OffChain         (MkTxError)
import           Wallet.Emulator.Error               (WalletAPIError)


-- | A payment consisting of a set of inputs to be spent, and
--   an optional change output. The size of the payment is the
--   difference between the total value of the inputs and the
--   value of the output.
data Payment =
    Payment
        { paymentInputs       :: Set.Set TxIn
        , paymentChangeOutput :: Maybe TxOut
        } deriving stock (Eq, Show, Generic)
          deriving anyclass (ToJSON, FromJSON)

-- | An error
newtype MatchingError = WrongVariantError { unWrongVariantError :: Text }
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (Aeson.ToJSON, Aeson.FromJSON)
makeClassyPrisms ''MatchingError
instance Pretty MatchingError where
  pretty = \case
    WrongVariantError t -> "Wrong variant:" <+> pretty t

-- | An error emitted when an 'Assertion' fails.
newtype AssertionError = GenericAssertion { unAssertionError :: T.Text }
    deriving stock (Show, Eq, Generic)
    deriving anyclass (ToJSON, FromJSON)
makeClassyPrisms ''AssertionError

instance Pretty AssertionError where
    pretty = \case
        GenericAssertion t -> "Generic assertion:" <+> pretty t

-- | This lets people use 'T.Text' as their error type.
instance AsAssertionError T.Text where
    _AssertionError = prism' (T.pack . show) (const Nothing)

data ContractError =
    WalletError WalletAPIError
    | EmulatorAssertionError AssertionError -- TODO: Why do we need this constructor
    | OtherError T.Text
    | ConstraintResolutionError MkTxError
    | ResumableError MatchingError
    | CCheckpointError CheckpointError
    deriving stock (Show, Eq, Generic)
    deriving anyclass (Aeson.ToJSON, Aeson.FromJSON)
makeClassyPrisms ''ContractError

instance Pretty ContractError where
  pretty = \case
    WalletError e               -> "Wallet error:" <+> pretty e
    EmulatorAssertionError a    -> "Emulator assertion error:" <+> pretty a
    OtherError t                -> "Other error:" <+> pretty t
    ConstraintResolutionError e -> "Constraint resolution error:" <+> pretty e
    ResumableError e            -> "Resumable error:" <+> pretty e
    CCheckpointError e          -> "Checkpoint error:" <+> pretty e

-- | This lets people use 'T.Text' as their error type.
instance AsContractError T.Text where
    _ContractError = prism' (T.pack . show) (const Nothing)

instance IsString ContractError where
  fromString = OtherError . fromString

instance AsAssertionError ContractError where
    _AssertionError = _EmulatorAssertionError

instance AsCheckpointError ContractError where
  _CheckpointError = _CCheckpointError

-- | Unique ID for contract instance
newtype ContractInstanceId = ContractInstanceId { unContractInstanceId :: UUID }
    deriving (Eq, Ord, Show, Generic)
    deriving newtype (FromJSONKey, ToJSONKey)
    deriving anyclass (FromJSON, ToJSON)
    deriving Pretty via (PrettyShow UUID)

-- | A pure list of all 'ContractInstanceId' values. To be used in testing.
contractInstanceIDs :: [ContractInstanceId]
contractInstanceIDs = ContractInstanceId <$> UUID.mockUUIDs

randomID :: IO ContractInstanceId
randomID = ContractInstanceId <$> UUID.nextRandom

newtype EndpointDescription = EndpointDescription { getEndpointDescription :: String }
    deriving stock (Eq, Ord, Generic, Show, TH.Lift)
    deriving newtype (IsString, Pretty)
    deriving anyclass (ToJSON, FromJSON)

newtype EndpointValue a = EndpointValue { unEndpointValue :: a }
    deriving stock (Eq, Ord, Generic, Show)
    deriving anyclass (ToJSON, FromJSON)

deriving via (Tagged "EndpointValue:" (PrettyShow a)) instance (Show a => Pretty (EndpointValue a))

data Notification =
    Notification
        { notificationContractID       :: ContractInstanceId
        , notificationContractEndpoint :: EndpointDescription
        , notificationContractArg      :: Aeson.Value
        }
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty Notification where
    pretty Notification{notificationContractID,notificationContractEndpoint,notificationContractArg} =
        hang 2 $ vsep
            [ "Instance:" <+> pretty notificationContractID
            , "Endpoint:" <+> pretty notificationContractEndpoint
            , "Argument:" <+> viaShow notificationContractArg
            ]

data NotificationError =
    EndpointNotAvailable ContractInstanceId EndpointDescription
    | MoreThanOneEndpointAvailable ContractInstanceId EndpointDescription
    | InstanceDoesNotExist ContractInstanceId
    | OtherNotificationError ContractError
    | NotificationJSONDecodeError EndpointDescription Aeson.Value String -- ^ Indicates that the target contract does not have the expected schema
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty NotificationError where
    pretty = \case
        EndpointNotAvailable i ep -> "Endpoint" <+> pretty ep <+> "not available on" <+> pretty i
        MoreThanOneEndpointAvailable i ep -> "Endpoint" <+> pretty ep <+> "is exposed more than once on" <+> pretty i
        InstanceDoesNotExist i -> "Instance does not exist:" <+> pretty i
        OtherNotificationError e -> "Other notification error:" <+> pretty e
        NotificationJSONDecodeError ep vv e ->
                "Notification JSON decoding error:"
                    <+> pretty e
                    <> colon
                    <+> pretty (BSL8.unpack (JSON.encodePretty vv))
                    <+> pretty ep

makeClassyPrisms ''NotificationError

-- | A payment with zero inputs and no change output
emptyPayment :: Payment
emptyPayment = Payment { paymentInputs = Set.empty, paymentChangeOutput = Nothing }

-- | Information about transactions that spend or produce an output at
--   an address in a slot.
data AddressChangeResponse =
    AddressChangeResponse
        { acrAddress :: Address -- ^ The address
        , acrSlot    :: Slot -- ^ The slot
        , acrTxns    :: [Tx] -- ^ Transactions that were validated in the slot and spent or produced at least one output at the address.
        }
        deriving stock (Eq, Generic, Show)
        deriving anyclass (ToJSON, FromJSON)

instance Pretty AddressChangeResponse where
    pretty AddressChangeResponse{acrAddress, acrTxns, acrSlot} =
        hang 2 $ vsep
            [ "Address:" <+> pretty acrAddress
            , "Slot:" <+> pretty acrSlot
            , "Tx IDs:" <+> pretty (txId <$> acrTxns)
            ]

-- | Request for information about transactions that spend or produce
--   outputs at a specific address in a slot.
data AddressChangeRequest =
    AddressChangeRequest
        { acreqSlot    :: Slot -- ^ The slot
        , acreqAddress :: Address -- ^ The address
        }
        deriving stock (Eq, Generic, Show, Ord)
        deriving anyclass (ToJSON, FromJSON)

instance Pretty AddressChangeRequest where
    pretty AddressChangeRequest{acreqSlot, acreqAddress} =
        hang 2 $ vsep
            [ "Slot:" <+> pretty acreqSlot
            , "Address:" <+> pretty acreqAddress
            ]
