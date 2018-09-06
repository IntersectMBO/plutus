{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RecordWildCards   #-}
-- Disabled until we can use the Num.(*) for `Ratio Int`
-- {-# OPTIONS -fplugin=Language.Plutus.CoreToPLC.Plugin #-}
module Language.Plutus.Coordination.Contracts.Swap(
    Swap(..),
    swapValidator
    ) where

import           Language.Plutus.Coordination.Plutus
import           Language.Plutus.CoreToPLC.Plugin     (plc)
import qualified Language.Plutus.CoreToPLC.Primitives as Prim

import           Data.Ratio                           (Ratio)
-- Ord, Num and Eq are recognised by core-to-plc
import           Prelude                              (Bool, Either (..), Eq (..), Int, Num (..), Ord (..))

-- | A swap is an agreement to exchange cashflows at future dates. To keep
--  things simple, this is an interest rate swap (meaning that the cashflows are
--  interest payments on the same principal amount but with two different
--  interest rates, of which one is fixed and one is floating (varying with
--  time)) with only a single payment date.
--
--  At the beginning of the contract, the fixed rate is set to the expected
--  future value of the floating rate (so if the floating rate behaves as
--  expected, the two payments will be exactly equal).
--
data Swap = Swap
    { swapNotionalAmt     :: !Value
    , swapObservationTime :: !BlockHeight
    , swapFixedRate       :: !(Ratio Int) -- ^ Interest rate fixed at the beginning of the contract
    , swapFloatingRate    :: !Int -- ^ Interest rate whose value will be observed (by an oracle) on the day of the payment
    , swapFixedLeg        :: !PubKey
    , swapFloatingLeg     :: !PubKey
    , swapMargin          :: !Value -- ^ Margin deposited at the beginning of the contract to protect against default (one party failing to pay)
    , swapOracle          :: !PubKey -- ^ Public key of the oracle (see note [Oracles] in [[Language.Plutus.Coordination.Plutus]])
    }

-- | Validator script for the two transactions that initialise the swap.
--   See note [Swap Transactions]
--   See note [Contracts and Validator Scripts] in
--       Language.Plutus.Coordination.Contracts
swapValidator :: Swap -> PlutusTx
swapValidator _ = PlutusTx result where
    result = plc (\(redeemer :: OracleValue (Ratio Int)) () PendingTx{..} Swap{..} ->
        let
            infixr 3 &&
            (&&) :: Bool -> Bool -> Bool
            (&&) = Prim.error

            mn :: Int -> Int -> Int
            mn a b = if a < b then a else b

            mx :: Int -> Int -> Int
            mx a b = if a > b then a else b

            extractVerifyAt :: OracleValue (Ratio Int) -> PubKey -> Int -> BlockHeight -> Ratio Int
            extractVerifyAt = Prim.error

            round :: Ratio Int -> Int
            round = Prim.error

            -- | Convert an [[Int]] to a [[Ratio Int]]
            fromInt :: Int -> Ratio Int
            fromInt = Prim.error

            signedBy :: TxIn -> PubKey -> Bool
            signedBy = Prim.error

            infixr 3 ||
            (||) :: Bool -> Bool -> Bool
            (||) = Prim.error

            isPubKeyOutput :: TxOut a -> PubKey -> Bool
            isPubKeyOutput = Prim.error

            -- Verify the authenticity of the oracle value and compute
            -- the payments.
            rt = extractVerifyAt redeemer swapOracle swapFloatingRate swapObservationTime

            rtDiff :: Ratio Int
            rtDiff = rt - swapFixedRate
            amt = swapNotionalAmt

            amt' :: Ratio Int
            amt' = fromInt amt

            delta :: Ratio Int
            delta = amt' * rtDiff

            fixedPayment :: Int
            fixedPayment = round (amt' + delta)

            floatPayment :: Int
            floatPayment = round (amt' - delta)

            -- Compute the payouts (initial margin +/- the sum of the two
            -- payments), ensuring that it is at least 0 and does not exceed
            -- the total amount of money at stake (2 * margin)
            clamp :: Int -> Int
            clamp x = mn 0 (mx (2 * swapMargin) x)
            fixedRemainder = clamp (swapMargin - fixedPayment + floatPayment)
            floatRemainder = clamp (swapMargin - floatPayment + fixedPayment)

            -- The transaction must have one input from each of the
            -- participants.
            -- NOTE: Partial match until we have lists
            Tx (Right (t1, t2)) (Right (o1, o2)) = pendingTxTransaction

            -- Each participant must deposit the margin. But we don't know the
            -- order in which the participant's deposits are included in the
            -- inputs. So we use the two predicates iP1 and iP2 to check
            -- for the two possible orderings (in `inConditions`)

            -- True if the transaction input is the margin payment of the
            -- fixed leg
            iP1 :: TxIn -> Bool
            iP1 t = signedBy t swapFixedLeg && txOutRefValue (txInOutRef t) == swapMargin

            -- True if the transaction input is the margin payment of the
            -- floating leg
            iP2 :: TxIn -> Bool
            iP2 t = signedBy t swapFloatingLeg && txOutRefValue (txInOutRef t) == swapMargin

            inConditions = (iP1 t1  && iP2 t2) || (iP1 t2 && iP2 t1)

            -- The transaction must have two outputs, one for each of the
            -- participants, which equal the margin adjusted by the difference
            -- between fixed and floating payment

            -- True if the output is the payment of the fixed leg.
            ol1 :: TxOut a -> Bool
            ol1 o = isPubKeyOutput o swapFixedLeg && txOutValue o <= fixedRemainder

            -- True if the output is the payment of the floating leg.
            ol2 :: TxOut a -> Bool
            ol2 o = isPubKeyOutput o swapFloatingLeg && txOutValue o <= floatRemainder

            -- NOTE: I didn't include a check that the chain height is greater
            -- than the observation time. This is because the chain height is
            -- already part of the oracle value and we trust the oracle.

            outConditions = (ol1 o1 && ol2 o2) || (ol1 o2 && ol2 o1)


        in
        if inConditions && outConditions then () else Prim.error
        )

{- Note [Swap Transactions]

The swap involves three transactions at two different times.

1. At t=0. Each participant deposits the margin. The outputs are locked with
   the same validator script, `swapValidator`
2. At t=n. The value of the floating rate, and consequently the values of the
   two payments are determined. Each participant gets their margin plus or
   minus the actual payment.

There is a risk of losing out if the interest rate moves outside the range of
fixedRate +/- (margin / notional amount). In a real financial contract this
would be dealt with by agreeing a "Variation Margin". This means that the
margin is adjusted at predefined dates before the actual payment is due. If one
of the parties fails to make the variation margin payment, the contract ends
prematurely and the other party gets to keep both margins.

Plutus should be able to handle variation margins in a series of validation
scripts. But it seems to me that they could get quite messy so I don't want to
write them by hand :) We can probably use TH to generate them at compile time.

-}
