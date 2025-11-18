{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-| A Plutus Core debugger TUI application.

 The application has two stages: browsing for files to debug, and debugging.
 If the argument is a directory, it enters the browsing stage.
 If the argument is a file, it enters the debugging stage.
 If no argument is provided, it defaults to the current working directory. -}
module Debugger.TUI.Main (main) where

import AnyProgram.Compile
import AnyProgram.With
import Debugger.TUI.Draw
import Debugger.TUI.Event
import Debugger.TUI.Types
import GetOpt
import PlutusCore qualified as PLC
import PlutusCore.Error
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Pretty qualified as PLC
import PlutusCore.Pretty qualified as PP
import PlutusPrelude hiding ((^.))
import Types
import UntypedPlutusCore as UPLC
import UntypedPlutusCore.Core.Zip
import UntypedPlutusCore.Evaluation.Machine.Cek
import UntypedPlutusCore.Evaluation.Machine.SteppableCek.DebugDriver qualified as D
import UntypedPlutusCore.Evaluation.Machine.SteppableCek.Internal

import Brick.AttrMap qualified as B
import Brick.BChan qualified as B
import Brick.Focus qualified as B
import Brick.Main qualified as B
import Brick.Util qualified as B
import Brick.Widgets.Edit qualified as BE
import Control.Concurrent
import Control.Monad.Except (runExcept, tryError)
import Control.Monad.Primitive (unsafeIOToPrim)
import Control.Monad.ST (RealWorld)
import Data.Maybe
import GHC.IO (stToIO)
import Graphics.Vty qualified as Vty
import Graphics.Vty.CrossPlatform qualified as Vty
import Lens.Micro

{- Note [Budgeting implementation for the debugger]
To retrieve the budget(s) (spent and remaining), we cannot simply
rely on `CekState`: the debuggable version of CEK tries to closely match the original CEK and
so it also inherits its pluggable spenders/emitters approach. Thus, for the debugger as well
we need to construct a budget mode (incl. a spender function) so we can have proper
budget accounting.

We could go with implementing a custom budget mode specifically for the
debugger (e.g. one that can talk directly to brick via events), but we opted instead to reuse
the `counting` and `restricting` modes, already built for the original cek.
-}

debuggerAttrMap :: B.AttrMap
debuggerAttrMap =
  B.attrMap
    Vty.defAttr
    [ (BE.editAttr, Vty.white `B.on` Vty.rgbColor @Int 32 32 32)
    , (BE.editFocusedAttr, Vty.white `B.on` Vty.black)
    , (menuAttr, Vty.withStyle (Vty.white `B.on` darkGreen) Vty.bold)
    , (highlightAttr, Vty.blue `B.on` Vty.white)
    ]
  where
    darkGreen :: Vty.Color
    darkGreen = Vty.rgbColor @Int 0 100 0

main
  :: (?opts :: Opts)
  => SNaming n -> SAnn a -> UPLC.Program (FromName n) DefaultUni DefaultFun (FromAnn a) -> IO ()
main sn sa prog = do
  -- turn it to ast with names
  progN <- either (fail . show @FreeVariableError) pure $ uplcToOutName' sn SName prog
  let progWithTxSpans = case sa of
        SUnit -> mempty <$ progN -- empty srcspans
        STxSrcSpans -> progN

  -- make sure to not display annotations
  let progTextN = withA @PP.Pretty sa $ PP.displayPlc $ void progN

  -- the parsed prog with uplc.srcspan
  progWithUplcSpan <-
    either (fail . show @(PLC.Error DefaultUni DefaultFun PLC.SrcSpan)) pure $
      runExcept $
        PLC.runQuoteT $
          UPLC.parseScoped progTextN

  progWithDAnn <-
    either fail pure $
      runExcept $
        pzipWith DAnn progWithUplcSpan progWithTxSpans

  -- The communication "channels" at debugger-driver and at brick
  driverMailbox <- newEmptyMVar @(D.Cmd Breakpoints)
  -- chan size of 20 is used as default for builtin non-custom events (mouse,key,etc)
  brickMailbox <- B.newBChan @CustomBrickEvent 20

  let app :: B.App DebuggerState CustomBrickEvent ResourceName
      app =
        B.App
          { B.appDraw = drawDebugger
          , B.appChooseCursor = B.showFirstCursor
          , B.appHandleEvent = handleDebuggerEvent driverMailbox (Just $ _debugDir ?opts)
          , B.appStartEvent = pure ()
          , B.appAttrMap = const debuggerAttrMap
          }
      initialState =
        DebuggerState
          { _dsKeyBindingsMode = KeyBindingsHidden
          , _dsFocusRing =
              B.focusRing $
                catMaybes
                  [ Just EditorUplc
                  , EditorSource <$ (Just $ _debugDir ?opts)
                  , Just EditorReturnValue
                  , Just EditorLogs
                  ]
          , _dsUplcEditor = BE.editorText EditorUplc Nothing progTextN
          , _dsUplcHighlight = Nothing
          , _dsSourceEditor = Nothing
          , _dsSourceHighlight = Nothing
          , _dsReturnValueEditor =
              BE.editorText
                EditorReturnValue
                Nothing
                ""
          , _dsLogsEditor =
              BE.editorText
                EditorLogs
                Nothing
                ""
          , _dsVLimitBottomEditors = 20
          , _dsHLimitRightEditors = 100
          , _dsBudgetData =
              BudgetData
                { _budgetSpent = mempty
                , -- the initial remaining budget is based on the passed cli arguments
                  _budgetRemaining = _budget ?opts
                }
          }

  let builder = Vty.mkVty Vty.defaultConfig
  initialVty <- builder

  -- TODO: find out if the driver-thread exits when brick exits
  -- or should we wait for driver-thread?
  _dTid <- forkIO $ driverThread driverMailbox brickMailbox progWithDAnn (_budget ?opts)

  void $ B.customMain initialVty builder (Just brickMailbox) app initialState

{-| The main entrypoint of the driver thread.

 The driver operates in IO (not in BrickM): the only way to "influence" Brick is via the mailboxes -}
driverThread
  :: forall uni fun ann
   . (uni ~ DefaultUni, fun ~ DefaultFun, ann ~ DAnn)
  => MVar (D.Cmd Breakpoints)
  -> B.BChan CustomBrickEvent
  -> Program Name uni fun ann
  -> Maybe ExBudget
  -> IO ()
driverThread driverMailbox brickMailbox prog mbudget = do
  let term = prog ^. UPLC.progTerm
  ndterm <- case runExcept @FreeVariableError $ deBruijnTerm term of
    Right t -> pure t
    Left _ -> fail $ "deBruijnTerm failed: " <> PLC.displayPlc (void term)
  -- if user provided `--budget` the mode is restricting; otherwise just counting
  -- See Note [Budgeting implementation for the debugger]
  let exBudgetMode = case mbudget of
        Just budgetLimit -> coerceMode $ restricting $ ExRestrictingBudget budgetLimit
        _ -> coerceMode counting
  -- nilSlippage is important so as to get correct live up-to-date budget
  cekTransWithBudgetRead <-
    mkCekTrans
      -- TODO: get correct semantics variant
      PLC.defaultCekParametersForTesting
      exBudgetMode
      brickEmitter
      nilSlippage
  D.iterM (handle cekTransWithBudgetRead) $ D.runDriverT ndterm
  where
    -- this gets rid of the CountingSt/RestrictingSt newtype wrappers
    -- See Note [Budgeting implementation for the debugger]
    coerceMode
      :: Coercible cost ExBudget
      => ExBudgetMode cost uni fun
      -> ExBudgetMode ExBudget uni fun
    coerceMode = coerce

    -- Peels off one Free monad layer
    -- Note to self: for some reason related to implicit params I cannot turn the following
    -- into a let block and avoid passing exbudgetinfo as parameter
    handle
      :: s ~ RealWorld
      => (D.CekTrans uni fun ann s, ExBudgetInfo ExBudget uni fun s)
      -> D.DebugF uni fun ann Breakpoints (IO ())
      -> IO ()
    handle (cekTrans, exBudgetInfo) = \case
      D.StepF prevState k -> do
        stepRes <- liftCek $ tryError $ cekTrans prevState
        -- if error then handle it, otherwise "kontinue"
        case stepRes of
          Left e -> handleError exBudgetInfo e
          Right newState -> k newState
      D.InputF k -> handleInput >>= k
      D.DriverLogF text k -> handleLog text >> k
      D.UpdateClientF ds k -> handleUpdate exBudgetInfo ds >> k

    handleInput = takeMVar driverMailbox

    handleUpdate exBudgetInfo cekState = do
      bd <- readBudgetData exBudgetInfo
      B.writeBChan brickMailbox $ UpdateClientEvent bd cekState

    handleError exBudgetInfo e = do
      bd <- readBudgetData exBudgetInfo
      B.writeBChan brickMailbox $ CekErrorEvent bd e
    -- no kontinuation in case of error, the driver thread exits
    -- TODO: decide what should happen after the error occurs
    -- e.g. a user dialog to (r)estart the thread with a button

    handleLog = B.writeBChan brickMailbox . DriverLogEvent

    readBudgetData :: ExBudgetInfo ExBudget uni fun RealWorld -> IO BudgetData
    readBudgetData (ExBudgetInfo _ final cumulative) =
      stToIO (BudgetData <$> cumulative <*> (for mbudget $ const final))

    brickEmitter :: EmitterMode uni fun
    brickEmitter = EmitterMode $ \_ -> do
      -- the simplest solution relies on unsafeIOToPrim (here, unsafeIOToST)
      let emitter logs = for_ logs (unsafeIOToPrim . B.writeBChan brickMailbox . CekEmitEvent)
      pure $ CekEmitterInfo emitter (pure mempty)
