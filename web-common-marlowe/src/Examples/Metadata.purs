module Examples.Metadata where

import Data.Map (fromFoldable, empty)
import Data.Tuple.Nested ((/\))
import Marlowe.Extended (ContractType(..))
import Marlowe.Extended.Metadata (MetaData, emptyContractMetadata)

example :: MetaData
example = emptyContractMetadata

escrow :: MetaData
escrow =
  { contractType: Escrow
  , contractName: "Simple escrow"
  , contractDescription: "Regulates a money exchange between a \"Buyer\" and a \"Seller\". If there is a disagreement, an \"Arbiter\" will decide whether the money is refunded or paid to the \"Seller\"."
  , choiceDescriptions:
      ( fromFoldable
          [ "Confirm problem" /\ "Acknowledge there was a problem and a refund must be granted."
          , "Dismiss claim" /\ "The \"Arbiter\" does not see any problem with the exchange and the \"Seller\" must be paid."
          , "Dispute problem" /\ "The \"Seller\" disagrees with the \"Buyer\" about the claim that something went wrong."
          , "Everything is alright" /\ "The transaction was uneventful, \"Buyer\" agrees to pay the \"Seller\"."
          , "Report problem" /\ "The \"Buyer\" claims not having received the product that was paid for as agreed and would like a refund."
          ]
      )
  , roleDescriptions:
      ( fromFoldable
          [ "Arbiter" /\ "The party that will choose who gets the money in the event of a disagreement between the \"Buyer\" and the \"Seller\" about the outcome."
          , "Buyer" /\ "The party that wants to buy the item. Payment is made to the \"Seller\" if they acknowledge receiving the item."
          , "Seller" /\ "The party that wants to sell the item. They receive the payment if the exchange is uneventful."
          ]
      )
  , slotParameterDescriptions:
      ( fromFoldable
          [ "Buyer's deposit timeout" /\ "Deadline by which the \"Buyer\" must deposit the selling \"Price\" in the contract."
          , "Buyer's dispute timeout" /\ "Deadline by which, if the \"Buyer\" has not opened a dispute, the \"Seller\" will be paid."
          , "Seller's response timeout" /\ "Deadline by which, if the \"Seller\" has not responded to the dispute, the \"Buyer\" will be refunded."
          , "Timeout for arbitrage" /\ "Deadline by which, if the \"Arbiter\" has not resolved the dispute, the \"Buyer\" will be refunded."
          ]
      )
  , valueParameterDescriptions: (fromFoldable [ "Price" /\ "Amount of Lovelace to be paid by the \"Buyer\" for the item." ])
  }

escrowWithCollateral :: MetaData
escrowWithCollateral =
  { contractType: Escrow
  , contractName: "Escrow with collateral"
  , contractDescription: "Regulates a money exchange between a \"Buyer\" and a \"Seller\" using a collateral from both parties to incentivize collaboration. If there is a disagreement the collateral is burned."
  , choiceDescriptions:
      ( fromFoldable
          [ "Confirm problem" /\ "Acknowledge that there was a problem and a refund must be granted."
          , "Dispute problem" /\ "The \"Seller\" disagrees with the \"Buyer\" about the claim that something went wrong and the collateral will be burnt."
          , "Everything is alright" /\ "The exchange was successful and the \"Buyer\" agrees to pay the \"Seller\"."
          , "Report problem" /\ "The \"Buyer\" claims not having received the product that was paid for as agreed and would like a refund."
          ]
      )
  , roleDescriptions:
      ( fromFoldable
          [ "Buyer" /\ "The party that pays for the item on sale."
          , "Seller" /\ "The party that sells the item and gets the money if the exchange is successful."
          ]
      )
  , slotParameterDescriptions:
      ( fromFoldable
          [ "Collateral deposit by seller timeout" /\ "The deadline by which the \"Seller\" must deposit the \"Collateral amount\" in the contract."
          , "Deposit of collateral by buyer timeout" /\ "The deadline by which the \"Buyer\" must deposit the \"Collateral amount\" in the contract."
          , "Deposit of price by buyer timeout" /\ "The deadline by which the \"Buyer\" must deposit the \"Price\" in the contract."
          , "Dispute by buyer timeout" /\ "The deadline by which, if the \"Buyer\" has not opened a dispute, the \"Seller\" will be paid."
          , "Seller's response timeout" /\ "The deadline by which, if the \"Seller\" has not responded to the dispute, the \"Buyer\" will be refunded."
          ]
      )
  , valueParameterDescriptions:
      ( fromFoldable
          [ "Collateral amount" /\ "The amount of Lovelace to be deposited by both parties at the start of the contract to serve as an incentive for collaboration."
          , "Price" /\ "The amount of Lovelace to be paid by the \"Buyer\" as part of the exchange."
          ]
      )
  }

zeroCouponBond :: MetaData
zeroCouponBond =
  { contractType: ZeroCouponBond
  , contractName: "Zero Coupon Bond"
  , contractDescription: "A simple loan. The investor pays the issuer the discounted price at the start, and is repaid the full (notional) price at the end."
  , choiceDescriptions: empty
  , roleDescriptions:
      ( fromFoldable
          [ "Investor" /\ "The party that buys the bond at a discounted price, i.e. makes the loan."
          , "Issuer" /\ "The party that issues the bond, i.e. receives the loan."
          ]
      )
  , slotParameterDescriptions:
      ( fromFoldable
          [ "Initial exchange deadline" /\ "The \"Investor\" must deposit the discounted price of the bond before this deadline or the offer will expire."
          , "Maturity exchange deadline" /\ "The \"Issuer\" must deposit the full price of the bond before this deadline or it will default."
          ]
      )
  , valueParameterDescriptions:
      ( fromFoldable
          [ "Discounted price" /\ "The price in Lovelace of the Zero Coupon Bond at the start date."
          , "Notional" /\ "The full price in Lovelace of the Zero Coupon Bond."
          ]
      )
  }

couponBondGuaranteed :: MetaData
couponBondGuaranteed =
  { contractType: CouponBondGuaranteed
  , contractName: "Coupon Bond Guaranteed"
  , contractDescription: "Debt agreement between an \"Investor\" and an \"Issuer\". \"Investor\" will advance the \"Principal\" amount at the beginning of the contract, and the \"Issuer\" will pay back \"Interest instalment\" every 30 slots and the \"Principal\" amount by the end of 3 instalments. The debt is backed by a collateral provided by the \"Guarantor\" which will be refunded as long as the \"Issuer\" pays back on time."
  , choiceDescriptions: empty
  , roleDescriptions:
      ( fromFoldable
          [ "Guarantor" /\ "Provides a collateral in case the \"Issuer\" defaults."
          , "Investor" /\ "Provides the money that the \"Issuer\" borrows."
          , "Issuer" /\ "Borrows the money provided by the \"Investor\" and returns it together with three \"Interest instalment\"s."
          ]
      )
  , slotParameterDescriptions: empty
  , valueParameterDescriptions:
      ( fromFoldable
          [ "Interest instalment" /\ "Amount of Lovelace that will be paid by the \"Issuer\" every 30 slots for 3 iterations."
          , "Principal" /\ "Amount of Lovelace that will be borrowed by the \"Issuer\"."
          ]
      )
  }

swap :: MetaData
swap =
  { contractType: Swap
  , contractName: "Swap of Ada and dollar tokens"
  , contractDescription: "Takes Ada from one party and dollar tokens from another party, and it swaps them atomically."
  , choiceDescriptions: empty
  , roleDescriptions:
      ( fromFoldable
          [ "Ada provider" /\ "The party that provides the Ada."
          , "Dollar provider" /\ "The party that provides the dollar tokens."
          ]
      )
  , slotParameterDescriptions:
      ( fromFoldable
          [ "Timeout for Ada deposit" /\ "Deadline by which Ada must be deposited."
          , "Timeout for dollar deposit" /\ "Deadline by which dollar tokens must be deposited (must be after the deadline for Ada deposit)."
          ]
      )
  , valueParameterDescriptions:
      ( fromFoldable
          [ "Amount of Ada" /\ "Amount of Ada to be exchanged for dollars."
          , "Amount of dollars" /\ "Amount of dollar tokens to be exchanged for Ada."
          ]
      )
  }

contractForDifferences :: MetaData
contractForDifferences =
  { contractType: ContractForDifferences
  , contractName: "Contract for Differences"
  , contractDescription: "\"Party\" and \"Counterparty\" deposit 100 Ada and after 60 slots is redistributed depending on the change in a given trade price reported by \"Oracle\". If the price increases, the difference goes to \"Counterparty\"; if it decreases, the difference goes to \"Party\", up to a maximum of 100 Ada."
  , choiceDescriptions:
      ( fromFoldable
          [ "Price at beginning" /\ "Trade price at the beginning of the contract."
          , "Price at end" /\ "Trade price at the end of the contract."
          ]
      )
  , roleDescriptions:
      ( fromFoldable
          [ "Counterparty" /\ "Party that gets the difference in trade price if it increases."
          , "Oracle" /\ "Party that provides the trade price in real time."
          , "Party" /\ "Party that gets the difference in trade price if it decreases."
          ]
      )
  , slotParameterDescriptions: empty
  , valueParameterDescriptions: empty
  }

contractForDifferencesWithOracle :: MetaData
contractForDifferencesWithOracle =
  { contractType: ContractForDifferences
  , contractName: "Contract for Differences with Oracle"
  , contractDescription: "\"Party\" and \"Counterparty\" deposit 100 Ada and after 60 slots these assets are redistributed depending on the change in price of 100 Ada worth of dollars between the start and the end of the contract. If the price increases, the difference goes to \"Counterparty\"; if it decreases, the difference goes to \"Party\", up to a maximum of 100 Ada."
  , choiceDescriptions:
      ( fromFoldable
          [ "dir-adausd" /\ "Exchange rate ADA/USD at the beginning of the contract."
          , "inv-adausd" /\ "Exchange rate USD/ADA at the end of the contract."
          ]
      )
  , roleDescriptions:
      ( fromFoldable
          [ "Counterparty" /\ "Party that gets the difference in trade price if it increases."
          , "Party" /\ "Party that gets the difference in trade price if it decreases."
          , "kraken" /\ "Oracle party that provides the exchange rate for ADA/USD."
          ]
      )
  , slotParameterDescriptions: empty
  , valueParameterDescriptions: empty
  }
