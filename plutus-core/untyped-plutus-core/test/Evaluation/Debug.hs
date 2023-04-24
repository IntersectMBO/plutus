{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeSynonymInstances  #-}

module Evaluation.Debug
    ( test_debug
    ) where

import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import UntypedPlutusCore
import UntypedPlutusCore.Evaluation.Machine.SteppableCek.DebugDriver
import UntypedPlutusCore.Evaluation.Machine.SteppableCek.Internal

import Control.Monad.Reader
import Control.Monad.ST
import Control.Monad.Writer
import Data.ByteString.Lazy.Char8 qualified as BS
import Data.Void
import Prettyprinter
import Test.Tasty
import Test.Tasty.Golden
import UntypedPlutusCore.Evaluation.Machine.Cek

test_debug :: TestTree
test_debug = testGroup "debug" $
    fmap goldenVsDebug examples

-- i am not testing breakpoint functionality at the moment
type Breakpoints = Void
newtype EmptyAnn = EmptyAnn ()
    deriving newtype (Semigroup, Monoid)
instance Breakpointable EmptyAnn Breakpoints where
    hasBreakpoints _ = absurd

examples :: [(String, [Cmd Breakpoints], NTerm DefaultUni DefaultFun EmptyAnn)]
examples = [
             ("ex1", repeat Step, Delay mempty $ Error mempty)
           , ("ex2", replicate 4 Step, Force mempty $ Delay mempty $ Error mempty)
           , ("ex3", replicate 5 Step, Force mempty $ Delay mempty $ Error mempty)
           , ("ex4", repeat Step, Error mempty)
           ]

goldenVsDebug :: (TestName, [Cmd Breakpoints], NTerm DefaultUni DefaultFun EmptyAnn) -> TestTree
goldenVsDebug (name, cmds, term) =
    goldenVsString name
    ("untyped-plutus-core/test/Evaluation/Debug/" ++ name ++ ".golden")
    (pure $ BS.pack $ unlines $ mock cmds term)

-- A Mocking interpreter

mock :: [Cmd Breakpoints] -- ^ commands to feed
     -> NTerm DefaultUni DefaultFun EmptyAnn -- ^ term to debug
     -> [String] -- ^ mocking output
mock cmds t = runST $ unCekM $ do
    (cekTrans,_) <- mkCekTrans defaultCekParameters restrictingEnormous noEmitter defaultSlippage
    execWriterT $ flip runReaderT cmds $
        -- MAYBE: use cutoff or partialIterT to prevent runaway
        iterM (handle cekTrans) $ runDriverT t

-- Interpretation of the mocker
-------------------------------

handle :: forall uni fun s m.
         ( PrettyUni uni fun
         , MonadWriter [String] m, MonadReader [Cmd Breakpoints] m
         , PrimMonad m, PrimState m ~ s
         )
       => CekTrans uni fun EmptyAnn s
       -> DebugF uni fun EmptyAnn Breakpoints (m ()) -> m ()
handle cekTrans = \case
    StepF prevState k -> do
        eNewState <- liftCek $ tryError $ cekTrans prevState
        case eNewState of
            Right newState -> do
                tell [show $ "OldState:" <+> pretty prevState
                           <+> "NewState:" <+> pretty newState]
                k newState
            Left e -> tell [show $ "OldState:" <+> pretty prevState
                                <+> "NewState is Error:" <+> viaShow e]
                     -- no kontinuation, exit
    InputF k          -> handleInput k
    LogF text k       -> handleLog text >> k
    UpdateClientF _ k -> k -- ignore
  where
    handleInput :: (Cmd Breakpoints -> m ()) -> m ()
    handleInput k = do
        cmds <- ask
        case cmds of
            [] ->
                tell ["Early run out of commands"]
            (cmd:cmds') ->
                local (const cmds') $
                    -- continue by feeding the next command to continuation
                    k cmd

    handleLog :: String -> m ()
    handleLog = tell . pure
