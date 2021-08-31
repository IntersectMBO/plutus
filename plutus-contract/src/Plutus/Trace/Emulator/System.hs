{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-

Defines the system threads. One thread for each simulated agent, and a block
maker thread for the blockchain / network.

-}
module Plutus.Trace.Emulator.System
  ( launchSystemThreads
  , appendNewTipBlock
  ) where

import           Control.Monad                 (forM_, void)
import           Control.Monad.Freer
import           Control.Monad.Freer.Coroutine
import           Data.Foldable                 (traverse_)
import           Data.Maybe                    (maybeToList)
import qualified Data.Text                     as Text
import qualified Data.Text.Encoding            as Text
import           Wallet.Emulator.Chain         (ChainControlEffect, modifySlot, processBlock)
import           Wallet.Emulator.MultiAgent    (MultiAgentControlEffect, MultiAgentEffect, walletAction,
                                                walletControlAction)

import           Data.Hashable                 (hash)
import           Data.String                   (IsString (..))
import           Ledger                        (Block, Slot, TxId (..), eitherTx, txId)
import           Plutus.ChainIndex             (BlockId (..), ChainIndexControlEffect, Tip (Tip, TipAtGenesis),
                                                appendBlock, fromOnChainTx, getTip)
import           Plutus.Trace.Emulator.Types   (EmulatorMessage (..))
import           Plutus.Trace.Scheduler        (EmSystemCall, MessageCall (..), Priority (..), Tag, fork, mkSysCall,
                                                sleep)
import           Wallet.Emulator.NodeClient    (ChainClientNotification (..), clientNotify)
import           Wallet.Emulator.Wallet        (Wallet (..))

{- Note [Simulator Time]

Simulator time is measured in slots, and the current time is part of the state
of the emulated node. Advancing the clock is done by the 'blockMaker' thread, a
thread that does nothing but produce a new block & slot each time it is woken
up.

Threads that need to do to multiple things in the same slot (for example,
contract instances handling several requests) suspend themselves with the
'Normal' priority. The block maker thread suspends itself with 'Sleeping', so
every time it is woken up, all threads with the 'Normal' priority have been
processed. As a result, the simulated clock advances to the next slot whenever
there is nothing left to do in the current slot.

-}

{- Note [Simulated Agents]

Each of the simulated agents runs its own thread. The agent listens to block
added and slot changed notifications, and updates its chain index accordingly.

Every contract instance runs in the context of an agent. If we want to test how
a contract instance reacts to network issues, we can freeze the agent's thread
and unfreeze it later on. While frozen, the agent thread will not update its
internal chain index, so it keeps an outdated view of the blockchain. When the
thread is unfrozen, it will receive & process all blockchain events since the
last time it ran in the order they arrived. So no messages are dropped - they
just arrive later.

-}

-- | Start the system threads.
launchSystemThreads :: forall effs.
    ( Member ChainControlEffect effs
    , Member MultiAgentEffect effs
    , Member MultiAgentControlEffect effs
    )
    => [Wallet]
    -> Eff (Yield (EmSystemCall effs EmulatorMessage) (Maybe EmulatorMessage) ': effs) ()
launchSystemThreads wallets = do
    _ <- sleep @effs @EmulatorMessage Sleeping
    -- 1. Threads for updating the agents' states. See note [Simulated Agents]
    traverse_ (\w -> fork @effs @EmulatorMessage (agentTag w) Normal $ agentThread @effs w) wallets
    -- 2. Block maker thread. See note [Simulator Time]
    void $ fork @effs @EmulatorMessage blockMakerTag Normal (blockMaker @effs)

-- | Tag for an agent thread. See note [Thread Tag]
agentTag :: Wallet -> Tag
agentTag (Wallet i) = fromString ("W " <> show i)

-- | Tag for the block maker thread. See note [Thread Tag]
blockMakerTag :: Tag
blockMakerTag = "block maker"

-- | The block maker thread. See note [Simulator Time]
blockMaker :: forall effs effs2.
    ( Member ChainControlEffect effs2
    , Member (Yield (EmSystemCall effs EmulatorMessage) (Maybe EmulatorMessage)) effs2
    )
    => Eff effs2 ()
blockMaker = go where
    go = do
        newBlock <- processBlock
        newSlot <- modifySlot succ
        _ <- mkSysCall @effs Sleeping $ Left $ Broadcast $ NewSlot [newBlock] newSlot
        _ <- sleep @effs @EmulatorMessage @effs2 Sleeping
        go

-- | Thread for a simulated agent. See note [Simulated Agents]
agentThread :: forall effs effs2.
    ( Member MultiAgentEffect effs2
    , Member MultiAgentControlEffect effs2
    , Member (Yield (EmSystemCall effs EmulatorMessage) (Maybe EmulatorMessage)) effs2
    )
    => Wallet
    -> Eff effs2 ()
agentThread wllt = go where
    go = do
        e <- sleep @effs @EmulatorMessage Sleeping
        let clientNotis = maybeToList e >>= \case
                NewSlot blocks slot -> fmap BlockValidated blocks ++ [SlotChanged slot]
                _                   -> []
        forM_ clientNotis $ \n -> walletControlAction wllt $ clientNotify n

        currentTip <- walletAction wllt getTip
        walletControlAction wllt $ do
          case e of
            Just (NewSlot blocks slot) -> do
              appendNewTipBlock currentTip (concat blocks) slot
            _ -> return ()

        go

-- | Append a block to the chain index for a specific slot.
appendNewTipBlock ::
    ( Member ChainIndexControlEffect effs
    )
    => Tip -- ^ Most recent tip
    -> Block -- ^ List of transactions
    -> Slot -- ^ Next slot to append the block
    -> Eff effs ()
appendNewTipBlock lastTip block newSlot = do
  let nextBlockNo = case lastTip of TipAtGenesis -> 0
                                    Tip _ _ n    -> n + 1

  -- To calculate the hast of a block, we concat the tx ids, and
  -- apply 'hash' to the resulting string.
  let blockId = BlockId
              $ (Text.encodeUtf8 . Text.pack . show . hash)
              $ foldMap (getTxId . eitherTx txId txId) block
  let newTip = Tip newSlot blockId nextBlockNo
  appendBlock newTip (fmap fromOnChainTx block)
