{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ImplicitParams        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLists       #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}

module Evaluation.Debug
    ( test_debug
    ) where

import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Evaluation.Machine.MachineParameters
import UntypedPlutusCore
import UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Driver
import UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Internal

import Control.Monad.Except
import Control.Monad.RWS
import Data.ByteString.Lazy.Char8 qualified as BS
import Data.Proxy
import Data.Void
import Prettyprinter
import Test.Tasty
import Test.Tasty.Golden
import UntypedPlutusCore.Evaluation.Machine.Cek.StepCounter (newCounter)

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
    (BS.pack . unlines <$> mock cmds term)

-- A Mocking interpreter

mock :: [Cmd Breakpoints] -- ^ commands to feed
     -> NTerm DefaultUni DefaultFun EmptyAnn -- ^ term to debug
     -> IO [String] -- ^ mocking output
mock cmds = cekMToIO . runMocking . runDriver
    where
      MachineParameters cekCosts cekRuntime = defaultCekParameters

      runMocking :: (m ~ CekM DefaultUni DefaultFun s)
                 => FreeT (DebugF DefaultUni DefaultFun EmptyAnn Breakpoints) m ()
                 -> m [String]
      runMocking driver = do
          ctr <- newCounter (Proxy @CounterSize)
          let ?cekRuntime = cekRuntime
              ?cekEmitter = const $ pure ()
              ?cekBudgetSpender = CekBudgetSpender $ \_ _ -> pure ()
              ?cekCosts = cekCosts
              ?cekSlippage = defaultSlippage
              ?cekStepCounter = ctr
          -- MAYBE: use cutoff or partialIterT to prevent runaway
          fmap snd $ execRWST (iterTM handle driver) cmds ()

-- Interpretation of the mocker
-------------------------------

type Mocking uni fun s t m = ( PrettyUni uni fun, GivenCekReqs uni fun EmptyAnn s
                           , MonadTrans t
                           -- | the mock client feeds commands
                           , MonadReader [Cmd Breakpoints] (t m)
                           -- | and logs to some string output
                           , MonadWriter [String] (t m)
                           )

handle :: ( Mocking uni fun s t m
         , m ~ CekM uni fun s
         )
       => DebugF uni fun EmptyAnn Breakpoints (t m ()) -> t m ()
handle = \case
    StepF prevState k -> do
        eNewState <- lift $ tryHandleStep prevState
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

    -- more general as :: (MonadReader [Cmd] m, MonadWriter [String] m) => (Cmd -> m ()) -> m ()
    handleInput :: Mocking uni fun s t m => (Cmd Breakpoints -> t m ()) -> t m ()
    handleInput k = do
        cmds <- ask
        case cmds of
            [] ->
                tell ["Early run out of commands"]
            (cmd:cmds') ->
                local (const cmds') $
                    -- continue by feeding the next command to continuation
                    k cmd

    -- more general as handleLog :: (MonadWriter [String] m) => String -> m ()
    handleLog :: Mocking uni fun s t m => String -> t m ()
    handleLog = tell . pure
