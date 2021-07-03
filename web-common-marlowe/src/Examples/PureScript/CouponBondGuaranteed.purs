module Examples.PureScript.CouponBondGuaranteed
  ( contractTemplate
  , metaData
  , extendedContract
  ) where

import Prelude
import Data.BigInteger (BigInteger, fromInt)
import Examples.Metadata as Metadata
import Marlowe.Extended (Action(..), Case(..), Contract(..), Payee(..), Timeout(..), Value(..))
import Marlowe.Extended.Metadata (MetaData, ContractTemplate)
import Marlowe.Semantics (Party(..), Token(..))

contractTemplate :: ContractTemplate
contractTemplate = { metaData, extendedContract }

metaData :: MetaData
metaData = Metadata.couponBondGuaranteed

ada :: Token
ada = Token "" ""

guarantor :: Party
guarantor = Role "Guarantor"

investor :: Party
investor = Role "Investor"

issuer :: Party
issuer = Role "Issuer"

principal :: Value
principal = ConstantParam "Principal"

instalment :: Value
instalment = ConstantParam "Interest instalment"

guaranteedAmount :: BigInteger -> Value
guaranteedAmount instalments = AddValue (MulValue (Constant instalments) instalment) principal

lastInstalment :: Value
lastInstalment = AddValue instalment principal

deposit :: Value -> Party -> Party -> Timeout -> Contract -> Contract -> Contract
deposit amount by toAccount timeout timeoutContinuation continuation =
  When [ Case (Deposit toAccount by ada amount) continuation ]
    timeout
    timeoutContinuation

refundGuarantor :: Value -> Contract -> Contract
refundGuarantor amount continuation = Pay investor (Party guarantor) ada amount continuation

transfer :: Value -> Party -> Party -> Timeout -> Contract -> Contract -> Contract
transfer amount from to timeout timeoutContinuation continuation =
  deposit amount from to timeout timeoutContinuation
    $ Pay to (Party to) ada amount
        continuation

extendedContract :: Contract
extendedContract =
  deposit (guaranteedAmount (fromInt 3)) guarantor investor
    (Slot $ fromInt 300)
    Close
    $ transfer principal investor issuer
        (Slot $ fromInt 600)
        (refundGuarantor (guaranteedAmount (fromInt 3)) Close)
    $ transfer instalment issuer investor
        (Slot $ fromInt 900)
        Close
    $ refundGuarantor instalment
    $ transfer instalment issuer investor
        (Slot $ fromInt 1200)
        Close
    $ refundGuarantor instalment
    $ transfer lastInstalment issuer investor
        (Slot $ fromInt 1500)
        Close
    $ refundGuarantor lastInstalment
        Close
