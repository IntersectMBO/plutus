{-# LANGUAGE DataKinds                       #-}
{-# LANGUAGE DeriveAnyClass                  #-}
{-# LANGUAGE DeriveGeneric                   #-}
{-# LANGUAGE NoImplicitPrelude               #-}
{-# LANGUAGE ScopedTypeVariables             #-}
{-# LANGUAGE TemplateHaskell                 #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module Auction.English where
-- TRIM TO HERE

import           Language.PlutusTx
import           Language.PlutusTx.Prelude
import           Language.PlutusTx.StateMachine
import           Ledger
import qualified Ledger.Ada                     as A
import qualified Ledger.Value                   as V
import           Playground.Contract
import           Wallet

import           Control.Monad (void, when)
import           Control.Monad.Except           (MonadError (..))
import qualified Data.ByteString.Lazy.Char8     as C
import           Data.List                      (find)
import           Data.Maybe                     (maybeToList)
import qualified Data.Map.Strict                as Map
import qualified Data.Set                       as Set
import qualified Data.Text                      as T

-- The admin token is parameterized by a transaction
-- output, which in turn is given by the hash of a
-- transaction and the output index.
type Admin = (TxHash, Integer)

-- Convert the reference to an output to a hash-index
-- pair.
mkAdmin :: TxOutRef -> Admin
mkAdmin (TxOutRefOf h i) = (plcTxHash h, i)

-- We need no data in data- and redeemer-scripts,
-- so both can be of unit type.
type AdminValidator = () -> () -> PendingTx -> Bool

validateAdmin :: Admin -> AdminValidator
validateAdmin (h, i) () () tx =
       spendsOutput tx h i
    && case pendingTxOutputs tx of
        (o : _) -> V.valueOf
            (pendingTxOutValue o)
            (ownCurrencySymbol tx)
            adminTokenName
            == 1
        []      -> False

adminRedeemer :: RedeemerScript
adminRedeemer = RedeemerScript $$(compileScript [|| \(_ :: Sealed ()) -> () ||])

mkAdminValidator :: Admin -> ValidatorScript
mkAdminValidator = ValidatorScript
                       . applyScript $$(compileScript [|| validateAdmin ||])
                       . lifted

adminAddress :: Admin -> Address
adminAddress = scriptAddress . mkAdminValidator

adminSymbol :: Admin -> CurrencySymbol
adminSymbol admin = case validatorScriptHash $ mkAdminValidator admin of
    ValidatorHash h -> V.currencySymbol h

adminTokenName :: TokenName
adminTokenName = TokenName emptyByteString

-- The value of the admin token.
adminValue :: Admin -> Value
adminValue admin = V.singleton (adminSymbol admin) adminTokenName 1

data NonFungible = NonFungible
    { issuer        :: PubKey
    , adminCurrency :: CurrencySymbol
    } deriving (Show, Generic, ToJSON, FromJSON, ToSchema)

makeLift ''NonFungible

type NonFungibleValidator =
       ()
    -> TokenName
    -> PendingTx
    -> Bool

validateNonFungible :: NonFungible -> NonFungibleValidator
validateNonFungible nf () name tx =
       txSignedBy tx (issuer nf)
    && case (pendingTxInputs tx, pendingTxOutputs tx) of
        ([i], os@(o : _)) ->
            let inValue = pendingTxInValue i
            in     foldl f V.zero os
                    == (inValue `V.plus` v2)
                && pendingTxOutValue o
                    == (inValue `V.plus` v)
                && V.valueOf inValue s name == 0
                && V.valueOf
                    inValue
                    (adminCurrency nf)
                    adminTokenName
                   == 1
                && case pendingTxOutHashes o of
                    Just (vh, _) -> vh == ownHash tx
                    Nothing      -> False
        _                 -> False
  where
    s :: CurrencySymbol
    s = ownCurrencySymbol tx

    v, v2 :: Value
    v  = V.singleton s name 1
    v2 = v `V.plus` v

    f :: Value -> PendingTxOut -> Value
    f w o = w `V.plus` pendingTxOutValue o

mkNonFungibleRedeemer :: String -> RedeemerScript
mkNonFungibleRedeemer name =
    let s = $$(compileScript [|| \(t :: TokenName) (_ :: Sealed (HashedDataScript ())) -> t ||])
    in  RedeemerScript $ applyScript s $ lifted $ TokenName $ C.pack name

mkNonFungibleValidator :: NonFungible -> ValidatorScript
mkNonFungibleValidator = ValidatorScript
                       . applyScript $$(compileScript [|| validateNonFungible ||])
                       . lifted

nonFungibleAddress :: NonFungible -> Address
nonFungibleAddress = scriptAddress . mkNonFungibleValidator

nonFungibleSymbol :: NonFungible -> CurrencySymbol
nonFungibleSymbol nf = case validatorScriptHash $ mkNonFungibleValidator nf of
    ValidatorHash h -> V.currencySymbol h

nonFungibleValue :: NonFungible -> String -> Value
nonFungibleValue nf name = V.singleton
    (nonFungibleSymbol nf)
    (TokenName $ C.pack name)
    1

mkNonFungibleTxOut :: NonFungible -> Value -> TxOut
mkNonFungibleTxOut nf v =
    scriptTxOut
        v
        (mkNonFungibleValidator nf)
        unitData

hasAdminToken :: CurrencySymbol -> (TxOutRef, TxOut) -> Bool
hasAdminToken s (_, o) =
    V.valueOf (txOutValue o) s adminTokenName == 1

data EnglishAuction = EnglishAuction
    { eaSymbol :: CurrencySymbol -- <1>
    , eaName   :: TokenName      -- <2>
    , eaOwner  :: PubKey         -- <3>
    , eaMinBid :: Ada            -- <4>
    , eaMinInc :: Ada            -- <5>
    , eaEndBid :: Slot           -- <6>
    , eaFinish :: Slot           -- <7>
    } deriving (Show, Generic, ToJSON, FromJSON, ToSchema)

makeLift ''EnglishAuction

type EAState = ([(PubKey, Ada)], Bool)

initialEAData :: DataScript
initialEAData = DataScript $ lifted (([], False) :: EAState)

data EAAction =
      EABid PubKey Ada        -- <1>
    | EAClaimBid              -- <2>
    | EAClaimToken            -- <3>
    | EAReclaimBid PubKey Ada -- <4>
    | EAReclaimToken          -- <5>

makeLift ''EAAction

eaOutput :: PendingTx -> PendingTxOut
eaOutput tx = case uniqueElement (findContinuingOutputs tx) of
    Nothing -> traceErrorH "exactly one output to the same script expected"
    Just i  -> pendingTxOutputs tx !! i

highestBid :: EAState -> Maybe (PubKey, Ada)
highestBid ([]   , _) = Nothing
highestBid (x : _, _) = Just x

minNewBid :: EnglishAuction -> EAState -> Ada
minNewBid _  (_, True) = traceErrorH "bidding ended"
minNewBid ea s         = case highestBid s of
    Nothing        -> eaMinBid ea
    Just (_, ada') -> eaMinInc ea `A.plus` ada'

valueCorrect :: PendingTx -> (Value -> Value -> Bool) -> Bool
valueCorrect tx cont =
    let iv = pendingTxInValue (pendingTxIn tx)
        ov = pendingTxOutValue (eaOutput tx)
    in  cont iv ov

tokenValue :: EnglishAuction -> Value
tokenValue ea = V.singleton (eaSymbol ea) (eaName ea) 1

eaTransit' :: EnglishAuction -> EAAction -> EAState -> EAState
eaTransit' ea (EABid pk ada) s@(xs, _)
    | ada >= minNewBid ea s = ((pk, ada) : xs, False)                      -- <1>
    | otherwise             = traceErrorH "bid too low"

eaTransit' _ EAClaimBid (_,  True)  = traceErrorH "already claimed"
eaTransit' _ EAClaimBid ([], False) = traceErrorH "no bid to claim"
eaTransit' _ EAClaimBid (xs, False) = (xs, True)

eaTransit' _ EAClaimToken ([], _) = traceErrorH "no bid made"
eaTransit' _ EAClaimToken s       = s

eaTransit' _ (EAReclaimBid _ _)    ([], _)     = traceErrorH "no bid made"
eaTransit' _ (EAReclaimBid pk ada) (y : ys, c) = (y : go ys, c)            -- <2>
  where
    go []                = traceErrorH "no such bid"
    go (z : zs)
        | z == (pk, ada) = zs
        | otherwise      = z : go zs

eaTransit' _ EAReclaimToken (_ : _, _) = traceErrorH "bid made"
eaTransit' _ EAReclaimToken ([], _)    = ([], False)

updateEAData :: EnglishAuction
             -> EAAction
             -> DataScript
             -> DataScript
updateEAData ea a (DataScript script) = DataScript $
    $$(compileScript [|| eaTransit' ||])
    `applyScript` lifted ea
    `applyScript` lifted a
    `applyScript` script

eaTransit :: EnglishAuction
          -> EAState
          -> EAAction
          -> PendingTx
          -> EAState
eaTransit ea s a@(EABid _ ada) tx
    | not validBidTime = traceErrorH "bid too late"
    | not bidPaid      = traceErrorH "wrong output value"
    | otherwise        = eaTransit' ea a s
  where
    validBidTime :: Bool                                  -- <1>
    validBidTime =
        intervalTo (eaEndBid ea)
            `contains` pendingTxValidRange tx

    bidPaid :: Bool
    bidPaid = valueCorrect tx (\iv ov ->                  -- <2>
        ov == (iv `V.plus` A.toValue ada))

eaTransit ea s a@EAClaimBid tx = case highestBid s of
    Nothing                  -> traceErrorH "no bid to claim"
    Just (_, ada)
        | not bidClaimed     -> traceErrorH "wrong value claimed"
        | not validClaimTime -> traceErrorH "claim too early"
        | not byOwner        -> traceErrorH "not claimed by owner"
        | otherwise          -> eaTransit' ea a s
      where
        bidClaimed :: Bool
        bidClaimed = valueCorrect tx (\iv ov ->                    -- <1>
            ov == (iv `V.minus` A.toValue ada))

        validClaimTime :: Bool                                     -- <2>
        validClaimTime =
            intervalFrom (eaEndBid ea)
                `contains` pendingTxValidRange tx

        byOwner :: Bool                                            -- <3>
        byOwner = tx `txSignedBy` eaOwner ea

eaTransit ea s a@EAClaimToken tx = case highestBid s of
    Nothing                   -> traceErrorH "no bid made"
    Just (pk, _)
        | not tokenClaimed    -> traceErrorH "wrong value claimed"
        | not validClaimTime  -> traceErrorH "claim too early"
        | not byHighestBidder -> traceErrorH "not claimed by highest bidder"
        | otherwise           -> eaTransit' ea a s
      where
        tokenClaimed :: Bool
        tokenClaimed = valueCorrect tx (\iv ov ->                            -- <1>
            ov == (iv `V.minus` tokenValue ea))

        validClaimTime :: Bool                                               -- <2>
        validClaimTime =
            intervalFrom (eaFinish ea)
                `contains` pendingTxValidRange tx

        byHighestBidder :: Bool                                              -- <3>
        byHighestBidder = tx `txSignedBy` pk

eaTransit ea s a@(EAReclaimBid pk ada) tx
    | not byBidder = traceErrorH "not reclaimed by bidder"
    | not correct  = traceErrorH "wrong value reclaimed"
    | otherwise    = eaTransit' ea a s
  where
    byBidder :: Bool
    byBidder = tx `txSignedBy` pk                          -- <1>

    correct :: Bool
    correct = valueCorrect tx (\iv ov ->                   -- <2>
        ov == (iv `V.minus` A.toValue ada))

eaTransit ea s a@EAReclaimToken tx
    | not validReclaimTime = traceErrorH "reclaim too early"
    | otherwise            = eaTransit' ea a s
  where
    validReclaimTime :: Bool
    validReclaimTime =
        intervalFrom (eaEndBid ea)
            `contains` pendingTxValidRange tx                -- <1>

-- FIXME: I've included this usecase for testing since it threw up some bugs
-- however due to https://github.com/input-output-hk/plutus/commit/54730c72aa8d44e1068fe15e70e092e8d732700d#diff-3e7e36b5b1f67216846635171b2786f7
-- these are just placeholder functions and need to be fixed by Lars Brunjes
-- especially if we want to use this example for further tests
eaStateMachine :: EnglishAuction -> StateMachine EAState EAAction
eaStateMachine ea = StateMachine (\_ _ -> Nothing) (\_ _ _ -> True)

mkEAValidator :: EnglishAuction -> ValidatorScript
mkEAValidator ea = ValidatorScript $
    $$(compileScript [|| \(ea' :: EnglishAuction) ->
        mkValidator (eaStateMachine ea') ||])
    `applyScript`
    lifted ea

eaAddress :: EnglishAuction -> Address
eaAddress = scriptAddress . mkEAValidator

mkEARedeemer :: EAAction -> RedeemerScript
mkEARedeemer a = RedeemerScript $
    $$(compileScript [||
        (mkRedeemer :: EAAction -> StateMachineRedeemer EAState EAAction) ||])
    `applyScript`
    lifted a

start :: forall m. MonadWallet m => m CurrencySymbol
start = do

    key  <- ownPubKey
    outs <- outputsAt $ pubKeyAddress key
    case Map.toList outs of
        []             -> throwError $
            OtherError $ T.pack "need at least one output"
        ((ref, o) : _) -> do
            let admin = mkAdmin ref
            startWatching $ adminAddress admin
            logMsg $ T.pack $
                "starting admin " ++ show admin
            void $ createTxAndSubmit
                defaultSlotRange
                Set.empty
                [scriptTxOut
                    V.zero
                    (mkAdminValidator admin)
                    unitData]
            go1 ref $ txOutValue o
            pure (adminSymbol admin)

  where
    go1 :: TxOutRef -> Value -> m ()
    go1 ref v = do
        t <- trigger
        registerOnce t $ handler1 ref v

    trigger :: m EventTrigger
    trigger = do
        sl <- slot
        return $ slotRangeT $ intervalFrom $ sl + 1

    handler1 :: TxOutRef -> Value -> EventHandler m
    handler1 ref v = EventHandler $ const $ do
        let admin = mkAdmin ref
        outs <- outputsAt $ adminAddress admin
        case Map.keys outs of
            []         -> go1 ref v
            (ref' : _) -> do
                key <- ownPubKey
                let i1 = pubKeyTxIn ref key
                    i2 = scriptTxIn
                            ref'
                            (mkAdminValidator admin)
                            unitRedeemer
                    o  = pubKeyTxOut
                            (v `V.plus` adminValue admin)
                            key
                signTxAndSubmit_ Tx
                    { txInputs     = Set.fromList [i1, i2]
                    , txOutputs    = [o]
                    , txFee        = A.zero
                    , txForge      = adminValue admin
                    , txValidRange = defaultSlotRange
                    , txSignatures = Map.empty
                    }
                logMsg $ T.pack $
                    "forging admin token " ++
                    show (adminSymbol admin)

                go2 (adminSymbol admin)

    go2 :: CurrencySymbol -> m ()
    go2 s = do
        t <- trigger
        registerOnce t $ handler2 s

    handler2 :: CurrencySymbol -> EventHandler m
    handler2 s = EventHandler $ const $ do
        key  <- ownPubKey
        outs <- outputsAt $ pubKeyAddress key
        case find (hasAdminToken s) $ Map.toList outs of
            Nothing       -> go2 s
            Just (ref, o) -> do
                let nf = NonFungible
                            { issuer        = key
                            , adminCurrency = s
                            }
                logMsg $ T.pack $
                    "starting tokens " ++ show nf
                let v  = V.singleton s adminTokenName 1
                    i  = pubKeyTxIn ref key
                    o1 = scriptTxOut
                            v
                            (mkNonFungibleValidator nf)
                            unitData
                    o2 = pubKeyTxOut
                            (txOutValue o `V.minus` v)
                            key
                void $ createTxAndSubmit
                    defaultSlotRange
                    (Set.singleton i)
                    [o1, o2]

forge :: forall m. MonadWallet m
      => CurrencySymbol -- admin token symbol
      -> String         -- token name
      -> m ()
forge s n = do

    key <- ownPubKey
    let nf = NonFungible
                { issuer        = key
                , adminCurrency = s
                }
    logMsg $ T.pack $
        "forging " ++ n ++ " of " ++ show nf

    outs <- outputsAt $ nonFungibleAddress nf
    case findOut s $ Map.toList outs of
        Just (ref, o) -> do
            let v    = nonFungibleValue nf n
                v2   = v `V.plus` v
                vIn  = txOutValue o
                vOut = vIn `V.plus` v
            signTxAndSubmit_ Tx
                { txInputs     = Set.singleton $ scriptTxIn
                                    ref
                                    (mkNonFungibleValidator nf)
                                    (mkNonFungibleRedeemer n)
                , txOutputs    = [ mkNonFungibleTxOut nf vOut
                                 , pubKeyTxOut v key
                                 ]
                , txFee        = A.zero
                , txForge      = v2
                , txValidRange = defaultSlotRange
                , txSignatures = Map.empty
                }
        _         -> throwError $
                        OtherError $ T.pack "'start' has not run"
  where
    findOut :: CurrencySymbol
            -> [(TxOutRef, TxOut)]
            -> Maybe (TxOutRef, TxOut)
    findOut = find . hasAdminToken

watchAuction :: MonadWallet m => EnglishAuction -> m ()
watchAuction ea = do
    logMsg $ T.pack $ "watching " ++ show ea
    startWatching $ eaAddress ea

startAuction :: MonadWallet m
             => CurrencySymbol
             -> TokenName
             -> Ada
             -> Ada
             -> Slot
             -> Slot
             -> m ()
startAuction s n b inc e f = do
    pk <- ownPubKey
    let ea = EnglishAuction
                { eaSymbol = s
                , eaName   = n
                , eaOwner  = pk
                , eaMinBid = b
                , eaMinInc = inc
                , eaEndBid = e
                , eaFinish = f
                }
    logMsg $ T.pack $
        "starting auction " ++ show ea

    payToScript_
        defaultSlotRange
        (eaAddress ea)
        (tokenValue ea)
        initialEAData

withAuctionOutput' :: MonadWallet m
                   => EnglishAuction
                   -> m a                                        -- <1>
                   -> (TxOutRef -> TxOut -> DataScript -> m a)   -- <2>
                   -> m a
withAuctionOutput' ea notFound cont = do
    outs <- outputsAt $ eaAddress ea
    case find containsToken $ Map.toList outs of
        Nothing       -> do
            logMsg $ T.pack $ "auction output not found"         -- <3>
            notFound
        Just (ref, o) -> do
            logMsg $ T.pack $ "found auction output: " ++ show o
            case txOutType o of
                PayToScript ds -> cont ref o ds                  -- <4>
                _              -> do
                    logMsg $ T.pack $ "not a script output"      -- <5>
                    notFound
  where
    containsToken :: (TxOutRef, TxOut) -> Bool                   -- <6>
    containsToken (_, o) = txOutValue o `V.geq` tokenValue ea

withAuctionOutput :: MonadWallet m
                  => EnglishAuction
                  -> (TxOutRef -> TxOut -> DataScript -> m ())
                  -> m ()
withAuctionOutput ea =
    withAuctionOutput' ea $ return ()

bid :: MonadWallet m
    => EnglishAuction
    -> Ada
    -> m ()
bid ea ada = do
    logMsg $ T.pack $
        "bidding " ++ show ada ++ " in " ++ show ea
    withAuctionOutput ea $ \ref o ds -> do                   -- <1>
        (ins, mo) <- createPaymentWithChange (A.toValue ada) -- <2>
        pk        <- ownPubKey
        let a   = EABid pk ada
            ds' = updateEAData ea a ds                       -- <3>
            v   = mkEAValidator ea
            i   = scriptTxIn ref v $ mkEARedeemer a          -- <4>
            o'  = scriptTxOut                                -- <5>
                    (txOutValue o `V.plus` A.toValue ada)
                    v
                    ds'
        signTxAndSubmit_ Tx
            { txInputs     = Set.insert i ins
            , txOutputs    = o' : maybeToList mo
            , txForge      = V.zero
            , txFee        = A.zero
            , txValidRange = intervalTo $ eaEndBid ea        -- <6>
            , txSignatures = Map.empty
            }

claimBid :: MonadWallet m
         => CurrencySymbol
         -> TokenName
         -> Ada
         -> Ada
         -> Slot
         -> Slot
         -> Ada                                         -- <1>
         -> m ()
claimBid s n b inc e f ada = do
    pk <- ownPubKey
    let ea = EnglishAuction
                { eaSymbol = s
                , eaName   = n
                , eaOwner  = pk
                , eaMinBid = b
                , eaMinInc = inc
                , eaEndBid = e
                , eaFinish = f
                }
    logMsg $ T.pack $ "claiming bid in " ++ show ea
    withAuctionOutput ea $ \ref o ds -> do
        let a    = EAClaimBid
            ada' = A.toValue ada
            v    = mkEAValidator ea
            i    = scriptTxIn ref v $ mkEARedeemer a
            ds'  = updateEAData ea a ds
            o1   = scriptTxOut
                    (txOutValue o `V.minus` ada') v ds' -- <2>
            o2   = pubKeyTxOut ada' pk                  -- <3>
        signTxAndSubmit_ Tx
            { txInputs     = Set.singleton i
            , txOutputs    = [o1, o2]
            , txForge      = V.zero
            , txFee        = A.zero
            , txValidRange = intervalFrom $ eaEndBid ea -- <4>
            , txSignatures = Map.empty
            }

claimToken :: MonadWallet m => EnglishAuction -> m ()
claimToken ea = do
    logMsg $ T.pack $ "claiming token in " ++ show ea
    withAuctionOutput ea $ \ref o ds -> do
        pk <- ownPubKey
        let a   = EAClaimToken
            v   = mkEAValidator ea
            i   = scriptTxIn ref v $ mkEARedeemer a
            ds' = updateEAData ea a ds
            t   = tokenValue ea
            o1  = scriptTxOut
                    (txOutValue o `V.minus` t) v ds'     -- <1>
            o2  = pubKeyTxOut t pk                       -- <2>
        signTxAndSubmit_ Tx
            { txInputs     = Set.singleton i
            , txOutputs    = [o1, o2]
            , txForge      = V.zero
            , txFee        = A.zero
            , txValidRange = intervalFrom $ eaFinish ea  -- <3>
            , txSignatures = Map.empty
            }

reclaimBid :: MonadWallet m
           => EnglishAuction
           -> Ada
           -> m ()
reclaimBid ea ada = do
    logMsg $ T.pack $
        "reclaiming " ++ show ada ++ " from " ++ show ea
    withAuctionOutput ea $ \ref o ds -> do
        pk <- ownPubKey
        let a    = EAReclaimBid pk ada
            ada' = A.toValue ada
            v    = mkEAValidator ea
            i    = scriptTxIn ref v $ mkEARedeemer a
            ds'  = updateEAData ea a ds
            o1   = scriptTxOut
                    (txOutValue o `V.minus` ada') v ds'  -- <1>
            o2   = pubKeyTxOut ada' pk                   -- <2>
        signTxAndSubmit_ Tx
            { txInputs     = Set.singleton i
            , txOutputs    = [o1, o2]
            , txForge      = V.zero
            , txFee        = A.zero
            , txValidRange = defaultSlotRange            -- <3>
            , txSignatures = Map.empty
            }

reclaimToken :: MonadWallet m
             => CurrencySymbol
             -> TokenName
             -> Ada
             -> Ada
             -> Slot
             -> Slot
             -> m ()
reclaimToken s n b inc e f = do
    pk <- ownPubKey
    let ea = EnglishAuction
                { eaSymbol = s
                , eaName   = n
                , eaOwner  = pk
                , eaMinBid = b
                , eaMinInc = inc
                , eaEndBid = e
                , eaFinish = f
                }
    logMsg $ T.pack $ "reclaiming token from " ++ show ea
    withAuctionOutput ea $ \ref o ds -> do
        let a    = EAReclaimToken
            v    = mkEAValidator ea
            i    = scriptTxIn ref v $ mkEARedeemer a
            ds'  = updateEAData ea a ds
            o1   = scriptTxOut V.zero v ds'               -- <1>
            o2   = pubKeyTxOut (txOutValue o) pk          -- <2>
        signTxAndSubmit_ Tx
            { txInputs     = Set.singleton i
            , txOutputs    = [o1, o2]
            , txForge      = V.zero
            , txFee        = A.zero
            , txValidRange = intervalFrom $ eaEndBid ea   -- <3>
            , txSignatures = Map.empty
            }

trackAuction :: forall m s. MonadWallet m
             => EnglishAuction
             -> s                                     -- <1>
             -> (   Slot
                 -> Ada
                 -> DataScript
                 -> s
                 -> m (Maybe s))                      -- <2>
             -> m ()
trackAuction ea initS action = do
    sl <- slot
    wait sl 0 0 initS                                 -- <3>
  where
    wait :: Slot -> Ada -> Ada -> s -> m ()           -- <4>
    wait sl highest total s = do
        let sl' = sl + 1
        registerOnce
            (slotRangeT $ singleton sl')
            (EventHandler $ const $
                go sl' highest total s)

    go :: Slot -> Ada -> Ada -> s -> m ()
    go sl highest total s = withAuctionOutput'
        ea
        (wait sl highest total s) $                   -- <5>
        \_ o ds -> do                                 -- <6>
            let v        = txOutValue o
                total'   = A.fromInt $                -- <7>
                            V.valueOf
                                v
                                A.adaSymbol
                                A.adaToken
                highest' = if total' > total
                                then total' - total
                                else highest          -- <8>

            logMsg $ T.pack $
                "highest bid " ++ show highest' ++
                " in auction " ++ show ea

            ms <- action sl highest' ds s             -- <9>
            case ms of
                Nothing -> return ()
                Just s' -> wait sl highest' total' s' -- <10>

runAuction :: forall m. MonadWallet m
           => CurrencySymbol
           -> TokenName
           -> Ada
           -> Ada
           -> Slot
           -> Slot
           -> m ()
runAuction s n b inc e f = do
    pk <- ownPubKey
    let ea = EnglishAuction
                { eaSymbol = s
                , eaName   = n
                , eaOwner  = pk
                , eaMinBid = b
                , eaMinInc = inc
                , eaEndBid = e
                , eaFinish = f
                }
    logMsg $ T.pack $
        "run auction " ++ show ea

    startAuction s n b inc e f

    trackAuction ea () $ \sl highest _ () -> do
        if sl == eaEndBid ea then do            -- <1>
            if highest > 0 then                 -- <2>
                claimBid s n b inc e f highest
            else                                -- <3>
                reclaimToken s n b inc e f
            return Nothing                      -- <4>

        else return $ Just ()                   -- <5>

unliftBool :: Script -> Bool
unliftBool s = case evaluateScript Typecheck b of -- <1>
    Right _ -> True
    Left _  -> False
  where
    b :: Script
    b = $$(compileScript [|| \(x :: Bool) ->
            if x then () else error () ||])       -- <2>
        `applyScript` s

isHighestBidder :: PubKey -> EAState -> Bool
isHighestBidder pk s = case highestBid s of
    Nothing       -> False
    Just (pk', _) -> pk == pk'

isHighestBidderM :: MonadWallet m
                 => DataScript
                 -> m Bool
isHighestBidderM (DataScript ds) = do
    pk <- ownPubKey
    return $ unliftBool $
        $$(compileScript [|| isHighestBidder ||])
        `applyScript` lifted pk
        `applyScript` ds

autoBid :: forall m. MonadWallet m
        => EnglishAuction
        -> Ada                                              -- <1>
        -> m ()
autoBid ea ada = do
    let m = eaMinBid ea
    return ()
    when (ada >= m) $ do                                    -- <2>

        logMsg $ T.pack $
            "bidding automatically in " ++ show ea ++
            " with highest bid " ++ show ada
        watchAuction ea

        trackAuction ea Nothing $ \sl highest ds mAda -> do -- <3>
            winning <- isHighestBidderM ds                  -- <4>
            logMsg $ T.pack $ show winning
            when (not winning && sl <= eaEndBid ea) $
                case mAda of
                    Just ada' -> reclaimBid ea ada'         -- <5>
                    Nothing   -> return ()
            case ( compare sl $ eaEndBid ea
                 , compare sl $ eaFinish ea) of             -- <6>
                 (GT, EQ) -> do                             -- <7>
                    claimToken ea
                    return Nothing
                 (EQ, LT)
                    | winning   -> return $ Just Nothing    -- <8>
                    | otherwise -> return Nothing           -- <9>
                 (GT, LT) -> return $ Just Nothing          -- <10>
                 _
                    | winning   -> return $ Just mAda       -- <11>
                    | otherwise -> do
                        let ada' = max
                                (eaMinBid ea)
                                (highest + eaMinInc ea)     -- <12>
                        if ada' > ada
                            then return Nothing             -- <13>
                            else do
                                bid ea ada'
                                return $ Just $ Just ada'   -- <14>

$(mkFunctions
    [ 'start, 'forge, 'startAuction, 'watchAuction
    , 'bid, 'claimBid, 'claimToken, 'reclaimBid
    , 'reclaimToken, 'runAuction, 'autoBid
    ])