module Language.Marlowe.Actus where
import           Language.Marlowe
import           Wallet.API       (PubKey (..))


{-|
    A zero-coupon bond is a debt security that doesn't pay interest (a coupon)
    but is traded at a deep discount, rendering profit at maturity
    when the bond is redeemed for its full face value.
-}
zeroCouponBond :: PubKey -> PubKey -> Integer -> Integer -> Timeout -> Timeout -> Timeout -> Contract
zeroCouponBond issuer investor notional discount startDate maturityDate gracePeriod =
    -- prepare money for zero-coupon bond, before it could be used
    CommitCash (IdentCC 1) investor (Value (notional - discount)) startDate maturityDate
        (CommitCash (IdentCC 2) issuer (Value notional) startDate (maturityDate + gracePeriod)
            (When FalseObs startDate Null
                (Pay (IdentPay 1) investor issuer (Committed (IdentCC 1)) maturityDate
                    (When FalseObs maturityDate Null
                        (Pay (IdentPay 2) issuer investor (Committed (IdentCC 2))
                            (maturityDate + gracePeriod) Null)
                    )
                )
            )
            Null
        )
        Null

{-|
    A zero-coupon bond is a debt security that doesn't pay interest (a coupon)
    but is traded at a @discount@, rendering profit at @maturityDate@
    when the bond is redeemed for its full face @notional@ value.
    The @issuer@ is not forced to commit before @startDate@, hence it's a trusted bond,
    as the final payment can fail.
    If an @investor@ does not redeem the bond value during @gracePeriod@ after @maturityDate@
    the @issuer@ can keep the value.
-}
trustedZeroCouponBond :: PubKey -> PubKey -> Integer -> Integer -> Timeout -> Timeout -> Timeout -> Contract
trustedZeroCouponBond issuer investor notional discount startDate maturityDate gracePeriod =
    -- prepare money for zero-coupon bond, before it could be used
    -- if the issuer won't pull the payment, investor can redeem the commit after maturityDate
    CommitCash (IdentCC 1) investor (Value (notional - discount)) startDate maturityDate
        (When FalseObs startDate Null -- after startDate
            -- issuer can 'pull' the payment before maturityDate
            (Pay (IdentPay 1) investor issuer (Committed (IdentCC 1)) maturityDate
                -- issuer must commit a bond value before maturityDate
                -- issuer can redeem committed value if the inverstor won't 'pull' the payment
                -- within gracePeriod after maturityDate
                (CommitCash (IdentCC 2) issuer (Value notional) maturityDate (maturityDate + gracePeriod)
                    (When FalseObs maturityDate Null
                        (Pay (IdentPay 2) issuer investor (Committed (IdentCC 2))
                            (maturityDate + gracePeriod) Null))
                    Null
                )
            )
        )
        Null

{-|
    Zero coupon bond with @guarantor@ party, who secures @issuer@ payment with
    `guarantee` collateral.
-}
zeroCouponBondGuaranteed :: PubKey -> PubKey -> PubKey -> Integer -> Integer -> Timeout -> Timeout -> Timeout -> Contract
zeroCouponBondGuaranteed issuer investor guarantor notional discount startDate maturityDate gracePeriod =
    -- prepare money for zero-coupon bond, before it could be used
    CommitCash (IdentCC 1) investor (Value (notional - discount)) startDate maturityDate
        -- guarantor commits a 'guarantee' before startDate
        (CommitCash (IdentCC 2) guarantor (Value notional) startDate (maturityDate + gracePeriod)
            (When FalseObs startDate Null
                (Pay (IdentPay 1) investor issuer (Committed (IdentCC 1)) maturityDate
                    (CommitCash (IdentCC 3) issuer (Value notional) maturityDate (maturityDate + gracePeriod)
                        -- if the issuer commits the notional before maturity date pay from it, redeem the 'guarantee'
                        (Pay (IdentPay 2) issuer investor (Committed (IdentCC 3))
                            (maturityDate + gracePeriod) (RedeemCC (IdentCC 2) Null))
                        -- pay from the guarantor otherwise
                        (Pay (IdentPay 3) guarantor investor (Committed (IdentCC 2))
                            (maturityDate + gracePeriod) Null)
                    )
                )
            )
            Null
        )
        Null
