-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module PlutusTx.Compiler.Error
  ( CompileError
  , Error (..)
  , WithContext (..)
  , withContext
  , withContextM
  , throwPlain
  , pruneContext
  ) where

import PlutusIR.Compiler qualified as PIR

import Language.Haskell.TH qualified as TH
import PlutusCore qualified as PLC
import PlutusCore.Pretty qualified as PLC

import Control.Monad.Except

import Data.Text qualified as T
import Prettyprinter qualified as PP

{-| An error with some (nested) context. The integer argument to 'WithContextC' represents
the priority of the context when displaying it. Lower numbers are more prioritised. -}
data WithContext c e = NoContext e | WithContextC Int c (WithContext c e)
  deriving stock (Functor)

type CompileError uni fun ann = WithContext T.Text (Error uni fun ann)

withContext :: MonadError (WithContext c e) m => Int -> c -> m a -> m a
withContext p c act = catchError act $ \err -> throwError (WithContextC p c err)

withContextM :: MonadError (WithContext c e) m => Int -> m c -> m a -> m a
withContextM p mc act = do
  c <- mc
  catchError act $ \err -> throwError (WithContextC p c err)

throwPlain :: MonadError (WithContext c e) m => e -> m a
throwPlain = throwError . NoContext

pruneContext :: Int -> WithContext c e -> WithContext c e
pruneContext prio = \case
  NoContext e -> NoContext e
  WithContextC p c e ->
    let inner = pruneContext prio e in if p > prio then inner else WithContextC p c inner

instance (PP.Pretty c, PP.Pretty e) => PP.Pretty (WithContext c e) where
  pretty = \case
    NoContext e -> "Error:" PP.<+> (PP.align $ PP.pretty e)
    WithContextC _ c e ->
      PP.vsep
        [ PP.pretty e
        , "Context:" PP.<+> (PP.align $ PP.pretty c)
        ]

data Error uni fun a
  = PLCError !(PLC.Error uni fun a)
  | PIRError !(PIR.Error uni fun (PIR.Provenance a))
  | CompilationError !T.Text
  | UnsupportedError !T.Text
  | FreeVariableError !T.Text
  | InvalidMarkerError !String
  | CoreNameLookupError !TH.Name

instance (PLC.PrettyUni uni, PP.Pretty fun, PP.Pretty a) => PP.Pretty (Error uni fun a) where
  pretty = PLC.prettyPlcClassicSimple

instance
  (PLC.PrettyUni uni, PP.Pretty fun, PP.Pretty a)
  => PLC.PrettyBy PLC.PrettyConfigPlc (Error uni fun a)
  where
  prettyBy config = \case
    PLCError e -> PP.vsep ["Error from the PLC compiler:", PLC.prettyBy config e]
    PIRError e -> PP.vsep ["Error from the PIR compiler:", PLC.prettyBy config e]
    CompilationError e -> "Unexpected error during compilation, please report this to the Plutus team:" PP.<+> PP.pretty e
    UnsupportedError e -> "Unsupported feature:" PP.<+> PP.pretty e
    FreeVariableError e ->
      "Reference to a name which is not a local, a builtin, or an external INLINABLE function:"
        PP.<+> PP.pretty e
    InvalidMarkerError e -> "Found invalid marker, not applied correctly in expression" PP.<+> PP.pretty e
    CoreNameLookupError n -> "Unable to get Core name needed for the plugin to function: " PP.<+> PP.viaShow n
