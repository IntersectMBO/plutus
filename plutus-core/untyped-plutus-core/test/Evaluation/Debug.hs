{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ImplicitParams        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLists       #-}
{-# LANGUAGE OverloadedStrings     #-}
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

import Control.Monad.RWS
import Control.Monad.ST (RealWorld)

import Data.ByteString.Lazy.Char8 qualified as BS
import Data.Void

import Prettyprinter

import Test.Tasty
import Test.Tasty.Golden

test_debug :: TestTree
test_debug = testGroup "debug" $
    fmap goldenVsDebug examples

-- i am not testing breakpoint functionality at the moment
type Breakpoints = Void
newtype EmptyAnn = EmptyAnn ()
    deriving newtype (Semigroup, Monoid)
instance Breakpointable EmptyAnn Breakpoints where
    hasBreakpoints _ = absurd

examples :: [(String, [Cmd Breakpoints], DTerm DefaultUni DefaultFun EmptyAnn)]
examples = [
             ("ex1", repeat Step, Delay mempty $ Error mempty)
           , ("ex2", replicate 4 Step, Force mempty $ Delay mempty $ Error mempty)
           -- TODO: these break because they throw IO exception
           -- , ("ex4", replicate 5 Step, Force mempty $ Delay mempty $ Error mempty)
           -- , ("ex1", repeat Step, Error mempty)
           ]

goldenVsDebug :: (TestName, [Cmd Breakpoints], DTerm DefaultUni DefaultFun EmptyAnn) -> TestTree
goldenVsDebug (name, cmds, term) =
    goldenVsString name
    ("untyped-plutus-core/test/Evaluation/Debug/" ++ name ++ ".golden")
    (BS.pack . unlines <$> mock cmds term)

-- A Mocking interpreter

mock :: [Cmd Breakpoints] -- ^ commands to feed
     -> DTerm DefaultUni DefaultFun EmptyAnn -- ^ term to debug
     -> IO [String] -- ^ mocking output
mock cmds = cekMToIO . runMocking . runDriver
    where
      MachineParameters cekCosts cekRuntime = defaultCekParameters

      runMocking :: (m ~ CekM DefaultUni DefaultFun RealWorld)
                 => FreeT (DebugF DefaultUni DefaultFun EmptyAnn Breakpoints) m ()
                 -> m [String]
      runMocking driver =
          let ?cekRuntime = cekRuntime
              ?cekEmitter = const $ pure ()
              ?cekBudgetSpender = CekBudgetSpender $ \_ _ -> pure ()
              ?cekCosts = cekCosts
              ?cekSlippage = defaultSlippage
          in
              -- MAYBE: use cutoff or partialIterT to prevent runaway
              fmap snd $ execRWST (iterTM handle driver) cmds ()

-- Interpretation of the mocker
-------------------------------

type Mocking uni fun t m = ( PrettyUni uni fun, GivenCekReqs uni fun EmptyAnn RealWorld
                           , MonadTrans t
                           -- | the mock client feeds commands
                           , MonadReader [Cmd Breakpoints] (t m)
                           -- | and logs to some string output
                           , MonadWriter [String] (t m)
                           )

handle :: ( Mocking uni fun t m
         , m ~ CekM uni fun RealWorld
         )
       => DebugF uni fun EmptyAnn Breakpoints (t m ()) -> t m ()
handle = \case
    StepF prevState k -> do
        newState <- lift (handleStep prevState)
        tell [show $ "OldState:" <+> pretty prevState <+> "NewState:" <+> pretty newState]
        k newState
    InputF k          -> handleInput k
    LogF text k       -> handleLog text >> k
    UpdateClientF _ k -> k -- ignore
  where

    -- more general as :: (MonadReader [Cmd] m, MonadWriter [String] m) => (Cmd -> m ()) -> m ()
    handleInput :: Mocking uni fun t m => (Cmd Breakpoints -> t m ()) -> t m ()
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
    handleLog :: Mocking uni fun t m => String -> t m ()
    handleLog = tell . pure
