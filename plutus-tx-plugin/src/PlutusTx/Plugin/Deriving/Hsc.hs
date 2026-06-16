{-# LANGUAGE CPP #-}

module PlutusTx.Plugin.Deriving.Hsc
  ( addWarning
  , throwError
  )
where

import Control.Monad.IO.Class qualified as IO
import GHC qualified as Ghc
import GHC.Data.Bag qualified as Ghc
import GHC.Driver.Config.Diagnostic qualified as Ghc
import GHC.Driver.Errors.Types qualified as Ghc
import GHC.Plugins qualified as Ghc
import GHC.Types.Error qualified as Ghc
import GHC.Utils.Error qualified as Ghc
import GHC.Utils.Logger qualified as Ghc

-- | Adds a warning
addWarning :: Ghc.SrcSpan -> Ghc.SDoc -> Ghc.Hsc ()
addWarning srcSpan msgDoc = do
  logger <- Ghc.getLogger
  IO.liftIO $
    Ghc.logMsg
      logger
      Ghc.MCOutput
      srcSpan
      msgDoc

-- | Throws an error
throwError :: Ghc.SrcSpan -> Ghc.SDoc -> Ghc.Hsc a
throwError srcSpan msgDoc = do
  dynFlags <- Ghc.getDynFlags
  let diagOpts = Ghc.initDiagOpts dynFlags
      -- 1. Create the plain diagnostic
      innerDiag = Ghc.mkPlainDiagnostic Ghc.WarningWithoutFlag [] msgDoc
      -- 2. Use the 'GhcUnknownMessage' wrapper with a 'Simple' constructor.
      -- This bypasses the need for phase-specific types like DsMessage.
      diagnostic = wrapDiagnostic innerDiag
      -- 3. Create the envelope
      msg = Ghc.mkPlainMsgEnvelope diagOpts srcSpan diagnostic
  Ghc.throwErrors $ Ghc.mkMessages (Ghc.unitBag msg)

{-| Wrap a plain diagnostic as 'Ghc.GhcUnknownMessage'. CPP-shimmed because
'Ghc.UnknownDiagnostic' gained a 'Ghc.DiagnosticOpts' arg in GHC 9.10. -}
#if __GLASGOW_HASKELL__ >= 910
wrapDiagnostic innerDiag =
  Ghc.GhcUnknownMessage (Ghc.UnknownDiagnostic (const Ghc.NoDiagnosticOpts) innerDiag)
#else
wrapDiagnostic innerDiag =
  Ghc.GhcUnknownMessage (Ghc.UnknownDiagnostic innerDiag)
#endif
