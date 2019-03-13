{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}
{-
    A vesting contract in Plutus

    This is the fifth in a series of tutorials:
    
    1. [Plutus Tx](../../doctest/Tutorial/01-plutus-tx.md)
    2. [A guessing game](../../doctest/Tutorial/02-validator-scripts.md)
    3. [A crowdfunding campaign](../../doctest/Tutorial/03-wallet-api.md)
    4. [Working with the emulator](./Emulator.hs)
    5. A multi-stage contract (this tutorial)

-}
module Tutorial.Vesting where

import           GHC.Generics              (Generic)
import qualified Data.Map                  as Map
import qualified Data.Set                  as Set

import qualified Language.PlutusTx         as P
import           Ledger                    (Address, DataScript(..), RedeemerScript(..), Signature, Slot, TxOutRef, TxIn, ValidatorScript(..))
import qualified Ledger                    as L
import           Ledger.Ada                (Ada)
import qualified Ledger.Ada                as Ada
import qualified Ledger.Ada.TH             as ATH
import qualified Ledger.Interval           as Interval
import qualified Ledger.Validation         as V
import qualified Ledger.Value              as Value
import           Wallet                    (WalletAPI(..), WalletDiagnostics, PubKey)
import qualified Wallet                    as W
import qualified Wallet.API                as WAPI
import qualified Wallet.Emulator.Types     as EM

import           Tutorial.ExUtil

{- |
    A vesting contract.

    In this part of the tutorial we will implement a simple vesting scheme,
    where money is locked by a contract and may only be retrieved after some
    time has passed.

    This is our first example of a contract that covers multiple transactions,
    with a contract state that changes over time.

    In our vesting scheme the money will be released in two _tranches_ (parts):
    A smaller part will be available after an initial number of slots have
    passed, and the entire amount will be released at the end. The owner of the
    vesting scheme does not have to take out all the money at once: They can take out any amount up to the total that has been released so far. The remaining funds stay locked and can be retrieved later.

    Let's start with the data types.

-}

-- | Tranche of a vesting scheme.
data VestingTranche = VestingTranche {
    vestingTrancheDate   :: Slot,
    -- ^ When this tranche is released
    vestingTrancheAmount :: Ada
    -- ^ How much money is locked in this tranche
    } deriving (Generic)

P.makeLift ''VestingTranche

-- | A vesting scheme consisting of two tranches. Each tranche defines a date
--   (slot) after which an additional amount of money can be spent.
data Vesting = Vesting {
    vestingTranche1 :: VestingTranche,
    -- ^ First tranche

    vestingTranche2 :: VestingTranche,
    -- ^ Second tranche

    vestingOwner    :: PubKey
    -- ^ The recipient of the scheme (who is authorised to take out money once 
    --   it has been released)
    } deriving (Generic)

P.makeLift ''Vesting

-- | The total amount of Ada locked by a vesting scheme
totalVested :: Vesting -> Ada
totalVested (Vesting l r _) = Ada.plus (vestingTrancheAmount l) (vestingTrancheAmount r)

{- |

    What should our data and redeemer scripts be? The vesting scheme only has a 
    single piece of information that we need to keep track of, namely how much 
    money is still locked in the contract. We can get this information from the 
    contract's transaction output, so we don't need to store it in the data 
    script. The type of our data script is therefore `()`.

    The redeemer script should carry some proof that the retriever of the funds 
    is indeed the `vestingOwner` that was specified in the contract. This proof 
    takes the form of a transaction hash signed by the `vestingOwner`'s private 
    key. For this we use the type 'Ledger.Types.Signature'

    That gives our validator script the signature

    `Vesting -> Signature -> () -> PendingTx -> ()`

-}


vestingValidator :: Vesting -> ValidatorScript
vestingValidator v = ValidatorScript val where
    val = L.applyScript inner (L.lifted v)
    inner = $$(L.compileScript [|| \(scheme :: Vesting) () (sig :: Signature) (p :: V.PendingTx) ->
        let
            
            Vesting tranche1 tranche2 owner = scheme
            VestingTranche d1 a1 = tranche1
            VestingTranche d2 a2 = tranche2

            V.PendingTx _ _ _ _ _ range = p
            -- range :: SlotRange, validity range of the pending transaction

            -- We need the hash of this validator script in order to ensure 
            -- that the pending transaction locks the remaining amount of funds 
            -- at the contract address.
            ownHash = $$(V.ownHash) p

            -- The total amount of Ada that has been vested:
            totalAmount :: Ada
            totalAmount = $$(ATH.plus) a1 a2

            -- It will be useful to know the amount of money that has been 
            -- released so far. This means we need to check the current slot 
            -- against the slots 'd1' and 'd2', defined in 'tranche1' and 
            -- 'tranche2' respectively. But the only indication of the current 
            -- time that we have is the 'range' value of the pending 
            -- transaction 'p', telling us that the current slot is one of the 
            -- slots contained in 'range'.
            --
            -- We can think of 'd1' as an interval as well: It is 
            -- the open-ended interval starting with slot 'd1'. At any point 
            -- during this interval we may take out up to 'a1' Ada.
            d1Intvl = $$(Interval.from) d1

            -- Likewise for 'd2'
            d2Intvl = $$(Interval.from) d2

            -- Now we can compare the validity range 'range' against our two 
            -- intervals. If 'range' is completely contained in 'd1Intvl', then 
            -- we know for certain that the current slot is in 'd1Intvl', so the
            -- amount 'a1' of the first tranche has been released.
            inD1Intvl = $$(Interval.contains) d1Intvl range

            -- Likewise for 'd2'
            inD2Intvl = $$(Interval.contains) d2Intvl range

            released :: Ada
            released
                -- to compute the amount that has been released we need to 
                -- consider three cases:

                -- If we are in d2Intvl then the current slot is greater than 
                -- or equal to 'd2', so everything has been released:
                | inD2Intvl = totalAmount

                -- If we are not in d2Intvl but in d1Intvl then only the first
                -- tranche 'a1' has been released:
                | inD1Intvl = a1

                -- Otherwise nothing has been released yet
                | True      = $$(ATH.zero)

            -- And the following amount has not been released yet:
            unreleased :: Ada
            unreleased = $$(ATH.minus) totalAmount released

            -- To check whether the withdrawal is legitimate we need to
            -- 1. Ensure that the amount taken out does not exceed the current 
            --    limit
            -- 2. Compare the provded signature with the public key of the 
            --    vesting owner
            -- We will call these conditions con1 and con2.

            -- con1 is true if the amount that remains locked in the contract 
            -- is greater than or equal to 'unreleased'. We use the 
            -- `adaLockedBy` function to get the amount of Ada paid by pending
            -- transaction 'p' to the script address 'ownHash'. 
            con1 :: Bool
            con1 = 
                let remainsLocked = $$(V.adaLockedBy) p ownHash
                in $$(ATH.geq) remainsLocked unreleased

            -- con2 is true if the provided signature is of the pending 
            -- transaction (excluding witnesses) and was created by the
            -- scheme owner's public key
            con2 :: Bool
            con2 = $$(V.signsTransaction) sig owner p

        in 
            
            if $$(P.and) con1 con2
            then ()
            else $$(P.error) ($$(P.traceH) "Cannot withdraw" ())

        ||])

contractAddress :: Vesting -> Address
contractAddress vst = L.scriptAddress (vestingValidator vst)

{- |

    We need three endpoints:

    * 'vestFunds' to lock the funds in a vesting scheme
    * 'registerVestingScheme', used by the owner to start watching the scheme's address
    * 'withdraw', used by the owner to take out some funds.

    The first two are very similar to endpoints we defined for earlier 
    contracts.

-}

vestFunds :: (Monad m, WalletAPI m) => Vesting -> m ()
vestFunds vst = do
    let amt = Ada.toValue (totalVested vst)
        adr = contractAddress vst
        dataScript = DataScript (L.lifted ())
    W.payToScript_ W.defaultSlotRange adr amt dataScript

registerVestingScheme :: (WalletAPI m) =>  Vesting -> m ()
registerVestingScheme vst = startWatching (contractAddress vst)

{- |

    The last endpoint, `withdraw`, is different. We need to create a 
    transaction that spends the contract's current unspent transaction output 
    *and* puts the Ada that remains back at the script address.

-}
withdraw :: (Monad m, WalletAPI m) => Vesting -> Ada -> m ()
withdraw vst vl = do

    let address = contractAddress vst
        validator = vestingValidator vst

    -- We are going to use the wallet API to build the transaction "by hand", 
    -- that is without using 'collectFromScript'.
    -- The signature of 'createTxAndSubmit' is
    -- 'SlotRange -> Set.Set TxIn -> [TxOut] -> m Tx'. So we need a slot range, 
    -- a set of inputs and a list of outputs.

    -- The transaction's validity range should begin with the current slot and 
    -- last indefinitely.
    range <- fmap WAPI.intervalFrom WAPI.slot

    -- We need to sign the pending transaction with our private key, using the 
    -- wallet api.
    -- 
    -- NOTE: The part of the mockchain that deals with signatures currently 
    -- uses 'Int's to represent signatures, just like 'Int's are used for 
    -- public and private keys. We can therefore simply create a signature 
    -- value here, using the  wallet's 'ownSignature' function. 
    --
    -- Work that integrates proper cryptographic signatures with public and 
    -- private keys into the emulator is currently ongoing and will result 
    -- in changes to the way signatures are handled in the wallet API. In 
    -- particular the 'ownSignature' function will take an additional argument, 
    -- namely the value that is being signed.
    --
    sig <- WAPI.ownSignature

    -- The input should be the UTXO of the vesting scheme. We can get the 
    -- outputs at an address (as far as they are known by the wallet) with
    -- `outputsAt`, which returns a map of 'TxOutRef' to 'TxOut'. 
    utxos <- WAPI.outputsAt address

    let 
        -- the redeemer script with our signature
        redeemer  = RedeemerScript (L.lifted sig)

        -- Turn the 'utxos' map into a set of 'TxIn' values
        mkIn :: TxOutRef -> TxIn
        mkIn r = L.scriptTxIn r validator redeemer

        ins = Set.map mkIn (Map.keysSet utxos)

    -- Our transaction has either one or two outputs.
    -- If the scheme is finished (no money is left in it) then 
    -- there is only one output, a pay-to-pubkey output owned by
    -- us.
    -- If any money is left in the scheme then there will be an additional
    -- pay-to-script output locked by the vesting scheme's validator script
    -- that keeps the remaining value.

    -- We can create a public key output to our own key with 'ownPubKeyTxOut'.
    ownOutput <- W.ownPubKeyTxOut (Ada.toValue vl)

    -- Now to compute the difference between 'vl' and what is currently in the 
    -- scheme:
    let 
        currentlyLocked = Map.foldr (\txo vl' -> vl' `Value.plus` L.txOutValue txo) Value.zero utxos
        remaining = currentlyLocked `Value.minus` (Ada.toValue vl)

        otherOutputs = if Value.eq Value.zero remaining
                       then []
                       else [L.scriptTxOut remaining validator (DataScript (L.lifted ()))]
    
    -- Finally we have everything we need for `createTxAndSubmit`
    _ <- WAPI.createTxAndSubmit range ins (ownOutput:otherOutputs)

    pure ()

{- |

    With the endpoints defined we can write a trace for a successful run of the 
    scheme, in which we take out a small amount after the first tranche has 
    been released.

-}

vestingSuccess :: (WalletAPI m, WalletDiagnostics m) => EM.Trace m ()
vestingSuccess = do

    -- The scheme, saving a total of 60 Ada for pk1
    let scheme = Vesting 
                    (VestingTranche 5  (Ada.fromInt 20))
                    (VestingTranche 10 (Ada.fromInt 40))
                    pk1

    -- 1. Wallet 'w1' starts watching the contract address using the 
    --    'registerVestingScheme' endpoint.
    _ <- EM.walletAction w1 (registerVestingScheme scheme)
    
    -- -- 2. Wallet 'w2' locks 60 ada in the scheme
    _ <- EM.walletAction w2 (vestFunds scheme)

    -- 3. Process this transaction and notify all wallets. Here we add a total 
    --    of five blocks so that the first tranche is released.
    _ <- EM.addBlocksAndNotify [w1, w2] 5

    -- 4. 'w1' withdraws 10 Ada
    _ <- EM.walletAction w1 (withdraw scheme (Ada.fromInt 10))

    -- 5. Process this transaction and notify all wallets
    _ <- EM.addBlocksAndNotify [w1, w2] 1

    -- Done.
    pure ()

{- |

    E8. Run the `vestingSuccess` trace in the emulator. You can use the 
        functions `runTraceDist` and `runTraceLog` from `Ledger.ExUtil`
    >>> import Tutorial.ExUtil
    >>> runTraceDist vestingSuccess
    fromList [(Wallet {getWallet = 1},Value {getValue = [(CurrencySymbol 0,1010)]}),(Wallet {getWallet = 2},Value {getValue = [(CurrencySymbol 0,940)]})]

    E9. Write traces similar to `vestingSuccess` that

        * Take out all the funds after 10 slots
        * Take out 10 Ada after 5 blocks and the rest at the end
        * Take out all the funds at the beginning (inspect the logs to convince 
        yourself that it failed)

    E10. Write an extended version of `registerVestingScheme` that also 
         registers a trigger to collect the remaining funds at the end of the 
         scheme.

-}
