module Examples.Metadata where

import Prelude
import Data.Map as Map
import Data.Tuple.Nested ((/\))
import Marlowe.Extended (ContractType(..))
import Marlowe.Extended.Metadata (NumberFormat(..), MetaData, emptyContractMetadata, lovelaceFormat, oracleRatioFormat)
import Data.Map.Ordered.OMap as OMap

example :: MetaData
example = emptyContractMetadata

escrow :: MetaData
escrow =
  { contractType: Escrow
  , contractName: "Purchase"
  , contractShortDescription: "In this contract a _**seller**_ wants to sell an item (like a bicycle) to a _**buyer**_ for a _price_."
  , contractLongDescription: "Neither trusts each other, but they both trust a _**mediator**_. The _**buyer**_ pays the _price_ into the contract account: if both the _**buyer**_ and the _**seller**_ agree that the _**buyer**_ has received the item, then the _**seller**_ receives the _price_; if not, then the _**mediator**_ ensures that the _**buyer**_ gets their money back."
  , choiceInfo:
      ( Map.fromFoldable
          [ "Confirm problem"
              /\ { choiceFormat: DefaultFormat
                , choiceDescription: "Acknowledge there was a problem and a refund must be granted."
                }
          , "Dismiss claim"
              /\ { choiceFormat: DefaultFormat
                , choiceDescription: "The _**Mediator**_ does not see any problem with the exchange and the _**Seller**_ must be paid."
                }
          , "Dispute problem"
              /\ { choiceFormat: DefaultFormat
                , choiceDescription: "The _**Seller**_ disagrees with the _**Buyer**_ about the claim that something went wrong."
                }
          , "Everything is alright"
              /\ { choiceFormat: DefaultFormat
                , choiceDescription: "The transaction was uneventful, _**Buyer**_ agrees to pay the _**Seller**_."
                }
          , "Report problem"
              /\ { choiceFormat: DefaultFormat
                , choiceDescription: "The _**Buyer**_ claims not having received the product that was paid for as agreed and would like a refund."
                }
          ]
      )
  , roleDescriptions:
      ( Map.fromFoldable
          [ "Mediator" /\ "The mediator decides who is right in the case of dispute."
          , "Buyer" /\ "The buyer of the item."
          , "Seller" /\ "The seller of the item."
          ]
      )
  , slotParameterDescriptions:
      ( OMap.fromFoldable
          [ "Payment deadline" /\ "The _**buyer**_ must pay the _price_ of the item by this time, otherwise the contract is cancelled."
          , "Complaint deadline" /\ "The _**buyer**_ can only complain until this deadline, otherwise the contract will assume the transaction went smoothly and pay the _**seller**_."
          , "Complaint response deadline" /\ "If the _**buyer**_ complained, the _**seller**_ must respond before this deadline, otherwise the contract will assume there was a problem with the transaction and refund the _**buyer**_."
          , "Mediation deadline" /\ "If the _**buyer**_ and the _**seller**_ disagree, the _**mediator**_ must weigh in before this deadline, otherwise the contract will assume there was a problem with the transaction and refund the _**buyer**_."
          ]
      )
  , valueParameterInfo:
      ( OMap.fromFoldable
          [ "Price"
              /\ { valueParameterFormat: lovelaceFormat
                , valueParameterDescription: "The price of the item."
                }
          ]
      )
  }

escrowWithCollateral :: MetaData
escrowWithCollateral =
  { contractType: Escrow
  , contractName: "Escrow with collateral"
  , contractShortDescription: "In this contract a _**seller**_ wants to sell an item (like a bicycle) to a _**buyer**_ for a _price_."
  , contractLongDescription: "In order to incentivise collaboration between the _**seller**_ and the _**buyer**_, at the beginning of the contract both parties deposit the _collateral amount_ that is burned if the parties disagree."
  , choiceInfo:
      ( Map.fromFoldable
          [ "Confirm problem"
              /\ { choiceFormat: DefaultFormat
                , choiceDescription: "Acknowledge that there was a problem and a refund must be granted."
                }
          , "Dispute problem"
              /\ { choiceFormat: DefaultFormat
                , choiceDescription: "The _**Seller**_ disagrees with the _**Buyer**_ about the claim that something went wrong and the collateral will be burnt."
                }
          , "Everything is alright"
              /\ { choiceFormat: DefaultFormat
                , choiceDescription: "The exchange was successful and the _**Buyer**_ agrees to pay the _**Seller**_."
                }
          , "Report problem"
              /\ { choiceFormat: DefaultFormat
                , choiceDescription: "The _**Buyer**_ claims not having received the product that was paid for as agreed and would like a refund."
                }
          ]
      )
  , roleDescriptions:
      ( Map.fromFoldable
          [ "Buyer" /\ "The party that pays for the item on sale."
          , "Seller" /\ "The party that sells the item and gets the money if the exchange is successful."
          ]
      )
  , slotParameterDescriptions:
      ( OMap.fromFoldable
          [ "Collateral deposit by seller timeout" /\ "The deadline by which the _**Seller**_ must deposit the _**Collateral amount**_ in the contract."
          , "Deposit of collateral by buyer timeout" /\ "The deadline by which the _**Buyer**_ must deposit the _**Collateral amount**_ in the contract."
          , "Deposit of price by buyer timeout" /\ "The deadline by which the _**Buyer**_ must deposit the _**Price**_ in the contract."
          , "Dispute by buyer timeout" /\ "The deadline by which, if the _**Buyer**_ has not opened a dispute, the _**Seller**_ will be paid."
          , "Complaint deadline" /\ "The deadline by which, if the _**Seller**_ has not responded to the dispute, the _**Buyer**_ will be refunded."
          ]
      )
  , valueParameterInfo:
      ( OMap.fromFoldable
          [ "Collateral amount"
              /\ { valueParameterFormat: lovelaceFormat
                , valueParameterDescription: "The amount of Lovelace to be deposited by both parties at the start of the contract to serve as an incentive for collaboration."
                }
          , "Price"
              /\ { valueParameterFormat: lovelaceFormat
                , valueParameterDescription: "The amount of Lovelace to be paid by the _**Buyer**_ as part of the exchange."
                }
          ]
      )
  }

zeroCouponBond :: MetaData
zeroCouponBond =
  { contractType: ZeroCouponBond
  , contractName: "Loan"
  , contractShortDescription: "A simple loan: the _**borrower**_ borrows the _amount_ from the _**lender**_, and at the _payback deadline_ pays back the _amount_ plus _interest_."
  , contractLongDescription: "This is a high risk/high reward contract. There is no guarantee that the _**borrower**_ will pay back the loan. However there is an opportunity for the _**lender**_ to set a high _interest_ rate at the cost of taking on this risk."
  , choiceInfo: Map.empty
  , roleDescriptions:
      ( Map.fromFoldable
          [ "Lender" /\ "The party that lends the _amount_."
          , "Borrower" /\ "The party that borrows the _amount_."
          ]
      )
  , slotParameterDescriptions:
      ( OMap.fromFoldable
          [ "Loan deadline" /\ "The _**lender**_ needs to deposit the _amount_ by this time."
          , "Payback deadline" /\ "The _**borrower**_ needs to deposit the repayment (_amount_ plus _interest_) by this time."
          ]
      )
  , valueParameterInfo:
      ( OMap.fromFoldable
          [ "Interest"
              /\ { valueParameterFormat: lovelaceFormat
                , valueParameterDescription: "The interest paid by the _**borrower**_."
                }
          , "Amount"
              /\ { valueParameterFormat: lovelaceFormat
                , valueParameterDescription: "The amount borrowed by the _**borrower**_."
                }
          ]
      )
  }

couponBondGuaranteed :: MetaData
couponBondGuaranteed =
  { contractType: CouponBondGuaranteed
  , contractName: "Coupon Bond Guaranteed"
  , contractShortDescription: "Debt agreement between an _**Lender**_ and an _**Borrower**_ that must be repaid in 3 instalments."
  , contractLongDescription: "_**Lender**_ will advance the _**Principal**_ amount at the beginning of the contract, and the _**Borrower**_ will pay back _**Interest instalment**_ every 30 slots and the _**Principal**_ amount by the end of 3 instalments. The debt is backed by a collateral provided by the _**Guarantor**_ which will be refunded as long as the _**Borrower**_ pays back on time."
  , choiceInfo: Map.empty
  , roleDescriptions:
      ( Map.fromFoldable
          [ "Guarantor" /\ "Provides a collateral in case the _**Borrower**_ defaults."
          , "Lender" /\ "Provides the money that the _**Borrower**_ borrows."
          , "Borrower" /\ "Borrows the money provided by the _**Lender**_ and returns it together with three _**Interest instalment**_s."
          ]
      )
  , slotParameterDescriptions: mempty
  , valueParameterInfo:
      ( OMap.fromFoldable
          [ "Interest instalment"
              /\ { valueParameterFormat: lovelaceFormat
                , valueParameterDescription: "Amount of Lovelace that will be paid by the _**Borrower**_ every 30 slots for 3 iterations."
                }
          , "Principal"
              /\ { valueParameterFormat: lovelaceFormat
                , valueParameterDescription: "Amount of Lovelace that will be borrowed by the _**Borrower**_."
                }
          ]
      )
  }

swap :: MetaData
swap =
  { contractType: Swap
  , contractName: "Swap of Ada and dollar tokens"
  , contractShortDescription: "Atomically exchange of Ada and dollar tokens."
  , contractLongDescription: "Waits until one party deposits Ada and the other party deposits dollar tokens. If both parties collaborate it carries the exchange atomically, otherwise parties are refunded."
  , choiceInfo: Map.empty
  , roleDescriptions:
      ( Map.fromFoldable
          [ "Ada provider" /\ "The party that provides the Ada."
          , "Dollar provider" /\ "The party that provides the dollar tokens."
          ]
      )
  , slotParameterDescriptions:
      ( OMap.fromFoldable
          [ "Timeout for Ada deposit" /\ "Deadline by which Ada must be deposited."
          , "Timeout for dollar deposit" /\ "Deadline by which dollar tokens must be deposited (must be after the deadline for Ada deposit)."
          ]
      )
  , valueParameterInfo:
      ( OMap.fromFoldable
          [ "Amount of Ada"
              /\ { valueParameterFormat: DecimalFormat 0 "₳"
                , valueParameterDescription: "Amount of Ada to be exchanged for dollars."
                }
          , "Amount of dollars"
              /\ { valueParameterFormat: DecimalFormat 0 "$"
                , valueParameterDescription: "Amount of dollar tokens to be exchanged for Ada."
                }
          ]
      )
  }

contractForDifferences :: MetaData
contractForDifferences =
  { contractType: ContractForDifferences
  , contractName: "CFD"
  , contractShortDescription: "Contract For Differences. Two parties deposit Ada in a contract and after some time the Ada is redistributed among them depending on the change in price of an asset as reported by a third party (_**oracle**_)."
  , contractLongDescription: "At the beginning of the contract, _**party**_ and _**counterparty**_ deposit some Ada in the contract. At the end of the contract, all Ada deposited is redistributed depending on the change in price in Ada of an asset (as reported by the _**oracle**_). If the price in Ada of the asset increases, the difference goes to _**counterparty**_; if it decreases, the difference goes to _**party**_, up to a maximum of the amount deposited at the beginning."
  , choiceInfo:
      ( Map.fromFoldable
          [ "Price in first window"
              /\ { choiceFormat: DecimalFormat 6 "₳"
                , choiceDescription: "Price in ADA of the asset in the first window."
                }
          , "Price in second window"
              /\ { choiceFormat: DecimalFormat 6 "₳"
                , choiceDescription: "Price in ADA of the asset in the second window."
                }
          ]
      )
  , roleDescriptions:
      ( Map.fromFoldable
          [ "Counterparty" /\ "The _**counterparty**_ will get the difference in the price of the asset if it increases."
          , "Party" /\ "The _**party**_ will get the difference in the price of the asset if it decreases."
          , "Oracle" /\ "The _**oracle**_ provides the price of the asset at the beginning (first window) and at the end (second window) of the contract (in this case the _**oracle**_ provides the conversion rate between Ada and dollars)."
          ]
      )
  , slotParameterDescriptions:
      ( OMap.fromFoldable
          [ "Party deposit deadline" /\ "The _amount paid by party_ must be deposited by this deadline, otherwise the contract is cancelled."
          , "Counterparty deposit deadline" /\ "The _amount paid by counterparty_ must be deposited by this deadline, otherwise the contract is cancelled and money is refunded."
          , "First window beginning" /\ "The first _**oracle**_ reading must be taken after this."
          , "First window deadline" /\ "The first _**oracle**_ reading must be taken before this, otherwise the contract is cancelled and money is refunded."
          , "Second window beginning" /\ "The second _**oracle**_ reading must be taken after this."
          , "Second window deadline" /\ "The second _**oracle**_ reading must be taken before this, otherwise the contract is cancelled and money is refunded."
          ]
      )
  , valueParameterInfo:
      ( OMap.fromFoldable
          [ "Amount paid by party"
              /\ { valueParameterFormat: DecimalFormat 6 "₳"
                , valueParameterDescription: "Amount that the _**party**_ will deposit at the beginning of the contract."
                }
          , "Amount paid by counterparty"
              /\ { valueParameterFormat: DecimalFormat 6 "₳"
                , valueParameterDescription: "Amount that the _**counterparty**_ will deposit at the beginning of the contract."
                }
          ]
      )
  }

contractForDifferencesWithOracle :: MetaData
contractForDifferencesWithOracle =
  { contractType: ContractForDifferences
  , contractName: "CFD with Oracle"
  , contractShortDescription: "Contract For Differences with Oracle. Two parties deposit Ada in a contract and after some time the Ada is redistributed among them depending on the change in price of an asset."
  , contractLongDescription: "At the beginning of the contract, _**party**_ and _**counterparty**_ deposit some Ada in the contract. At the end of the contract, all Ada deposited is redistributed depending on the change in price in dollars of an asset (as reported by the _**oracle**_). The asset in this contract is an amount of Ada. If the price in dollars of the asset increases, the difference goes to _**counterparty**_; if it decreases, the difference goes to _**party**_, up to a maximum of the amount deposited at the beginning."
  , choiceInfo:
      ( Map.fromFoldable
          [ "dir-adausd"
              /\ { choiceFormat: oracleRatioFormat "ADA/USD"
                , choiceDescription: "Exchange rate ADA/USD in the first window."
                }
          , "inv-adausd"
              /\ { choiceFormat: oracleRatioFormat "USD/ADA"
                , choiceDescription: "Exchange rate USD/ADA in the second window."
                }
          ]
      )
  , roleDescriptions:
      ( Map.fromFoldable
          [ "Counterparty" /\ "The _**counterparty**_ will get the difference in the price of the asset if it increases."
          , "Party" /\ "The _**party**_ will get the difference in the price of the asset if it decreases."
          , "kraken" /\ "The _**oracle**_ provides the price of the asset at the beginning (first window) and at the end (second window) of the contract (in this case the _**oracle**_ provides the conversion rate between Ada and dollars)."
          ]
      )
  , slotParameterDescriptions:
      ( OMap.fromFoldable
          [ "Party deposit deadline" /\ "The _amount paid by party_ must be deposited by this deadline, otherwise the contract is cancelled."
          , "Counterparty deposit deadline" /\ "The _amount paid by counterparty_ must be deposited by this deadline, otherwise the contract is cancelled and money is refunded."
          , "First window beginning" /\ "The first _**oracle**_ reading must be taken after this."
          , "First window deadline" /\ "The first _**oracle**_ reading must be taken before this, otherwise the contract is cancelled and money is refunded."
          , "Second window beginning" /\ "The second _**oracle**_ reading must be taken after this."
          , "Second window deadline" /\ "The second _**oracle**_ reading must be taken before this, otherwise the contract is cancelled and money is refunded."
          ]
      )
  , valueParameterInfo:
      ( OMap.fromFoldable
          [ "Amount paid by party"
              /\ { valueParameterFormat: DecimalFormat 6 "₳"
                , valueParameterDescription: "Amount that the _**party**_ will deposit at the beginning of the contract."
                }
          , "Amount paid by counterparty"
              /\ { valueParameterFormat: DecimalFormat 6 "₳"
                , valueParameterDescription: "Amount that the _**counterparty**_ will deposit at the beginning of the contract."
                }
          , "Amount of Ada to use as asset"
              /\ { valueParameterFormat: DecimalFormat 6 "₳"
                , valueParameterDescription: "Amount of Ada whose price in dollars change to monitor."
                }
          ]
      )
  }
