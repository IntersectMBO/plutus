module Marlowe.Market.Contract4
  ( contractTemplate
  , metaData
  , extendedContract
  ) where

import Prelude
import Data.BigInteger (fromInt) as BigInteger
import Data.Map (fromFoldable)
import Data.Tuple.Nested ((/\))
import Marlowe.Extended (Action(..), Case(..), Contract(..), ContractType(..), Payee(..), Timeout(..), Value(..))
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.Extended.Template (ContractTemplate)
import Marlowe.Semantics (Party(..), Token(..))

contractTemplate :: ContractTemplate
contractTemplate = { metaData, extendedContract }

metaData :: MetaData
metaData =
  { contractType: CouponBondGuaranteed
  , contractName: "Coupon Bond Guaranteed"
  , contractDescription: "Debt agreement between an \"Investor\" and an \"Issuer\". \"Investor\" will advance the \"Principal\" amount at the beginning of the contract, and the \"Issuer\" will pay back \"Interest instalment\" every 30 slots and the \"Principal\" amount by the end of 3 instalments. The debt is backed by a collateral provided by the \"Guarantor\" which will be refunded as long as the \"Issuer\" pays back on time."
  , roleDescriptions:
      fromFoldable
        [ "Guarantor" /\ "Provides a collateral in case the \"Issuer\" defaults."
        , "Investor" /\ "Provides the money that the \"Issuer\" borrows."
        , "Issuer" /\ "Borrows the money provided by the \"Investor\" and returns it together with three \"Interest instalment\"s."
        ]
  , slotParameterDescriptions: mempty
  , valueParameterDescriptions:
      fromFoldable
        [ "Interest instalment" /\ "Amount of Lovelace that will be paid by the \"Issuer\" every 30 slots for 3 iterations."
        , "Principal" /\ "Amount of Lovelace that will be borrowed by the \"Issuer\"."
        ]
  , choiceDescriptions: mempty
  }

extendedContract :: Contract
extendedContract =
  When
    [ Case
        ( Deposit
            (Role "Investor")
            (Role "Guarantor")
            (Token "" "")
            ( AddValue
                ( MulValue
                    (Constant $ BigInteger.fromInt 3)
                    (ConstantParam "Interest instalment")
                )
                (ConstantParam "Principal")
            )
        )
        ( When
            [ Case
                ( Deposit
                    (Role "Issuer")
                    (Role "Investor")
                    (Token "" "")
                    (ConstantParam "Principal")
                )
                ( Pay
                    (Role "Issuer")
                    (Party (Role "Issuer"))
                    (Token "" "")
                    (ConstantParam "Principal")
                    ( When
                        [ Case
                            ( Deposit
                                (Role "Investor")
                                (Role "Issuer")
                                (Token "" "")
                                (ConstantParam "Interest instalment")
                            )
                            ( Pay
                                (Role "Investor")
                                (Party (Role "Investor"))
                                (Token "" "")
                                (ConstantParam "Interest instalment")
                                ( Pay
                                    (Role "Investor")
                                    (Party (Role "Guarantor"))
                                    (Token "" "")
                                    (ConstantParam "Interest instalment")
                                    ( When
                                        [ Case
                                            ( Deposit
                                                (Role "Investor")
                                                (Role "Issuer")
                                                (Token "" "")
                                                (ConstantParam "Interest instalment")
                                            )
                                            ( Pay
                                                (Role "Investor")
                                                (Party (Role "Investor"))
                                                (Token "" "")
                                                (ConstantParam "Interest instalment")
                                                ( Pay
                                                    (Role "Investor")
                                                    (Party (Role "Guarantor"))
                                                    (Token "" "")
                                                    (ConstantParam "Interest instalment")
                                                    ( When
                                                        [ Case
                                                            ( Deposit
                                                                (Role "Investor")
                                                                (Role "Issuer")
                                                                (Token "" "")
                                                                ( AddValue
                                                                    (ConstantParam "Interest instalment")
                                                                    (ConstantParam "Principal")
                                                                )
                                                            )
                                                            ( Pay
                                                                (Role "Investor")
                                                                (Party (Role "Investor"))
                                                                (Token "" "")
                                                                ( AddValue
                                                                    (ConstantParam "Interest instalment")
                                                                    (ConstantParam "Principal")
                                                                )
                                                                ( Pay
                                                                    (Role "Investor")
                                                                    (Party (Role "Guarantor"))
                                                                    (Token "" "")
                                                                    ( AddValue
                                                                        (ConstantParam "Interest instalment")
                                                                        (ConstantParam "Principal")
                                                                    )
                                                                    Close
                                                                )
                                                            )
                                                        ]
                                                        (Slot $ BigInteger.fromInt 150)
                                                        Close
                                                    )
                                                )
                                            )
                                        ]
                                        (Slot $ BigInteger.fromInt 120)
                                        Close
                                    )
                                )
                            )
                        ]
                        (Slot (BigInteger.fromInt 90))
                        Close
                    )
                )
            ]
            (Slot $ BigInteger.fromInt 60)
            ( Pay
                (Role "Investor")
                (Party (Role "Guarantor"))
                (Token "" "")
                ( AddValue
                    ( MulValue
                        (Constant $ BigInteger.fromInt 3)
                        (ConstantParam "Interest instalment")
                    )
                    (ConstantParam "Principal")
                )
                Close
            )
        )
    ]
    (Slot $ BigInteger.fromInt 30)
    Close
