{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
module PlutusTx.Compiler.Error (
    CompileError
    , Error (..)
    , WithContext (..)
    , withContext
    , withContextM
    , throwPlain
    , pruneContext) where

import qualified PlutusIR.Compiler         as PIR

import qualified Language.Haskell.TH       as TH
import qualified PlutusCore                as PLC
import qualified PlutusCore.Pretty         as PLC
import qualified PlutusIR                  as PIR

import           Control.Lens
import           Control.Monad.Except

import qualified Data.Text                 as T
import qualified Data.Text.Prettyprint.Doc as PP
import           ErrorCode

-- | An error with some (nested) context. The integer argument to 'WithContextC' represents
-- the priority of the context when displaying it. Lower numbers are more prioritised.
data WithContext c e = NoContext e | WithContextC Int c (WithContext c e)
    deriving Functor
makeClassyPrisms ''WithContext

type CompileError uni fun = WithContext T.Text (Error uni fun ())

instance HasErrorCode (CompileError _a _b) where
    errorCode (NoContext e)        = errorCode e
    errorCode (WithContextC _ _ w) = errorCode w

withContext :: (MonadError (WithContext c e) m) => Int -> c -> m a -> m a
withContext p c act = catchError act $ \err -> throwError (WithContextC p c err)

withContextM :: (MonadError (WithContext c e) m) => Int -> m c -> m a -> m a
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
        NoContext e     -> "Error:" PP.<+> (PP.align $ PP.pretty e)
        WithContextC _ c e -> PP.vsep [
            PP.pretty e,
            "Context:" PP.<+> (PP.align $ PP.pretty c)
            ]

data Error uni fun a = PLCError (PLC.Error uni fun a)
                 | PIRError (PIR.Error uni fun (PIR.Provenance a))
                 | CompilationError T.Text
                 | UnsupportedError T.Text
                 | FreeVariableError T.Text
                 | InvalidMarkerError String
                 | CoreNameLookupError TH.Name
makeClassyPrisms ''Error

instance HasErrorCode (Error _a _b _c) where
      errorCode CompilationError {}    = ErrorCode 41
      errorCode UnsupportedError {}    = ErrorCode 42
      errorCode FreeVariableError {}   = ErrorCode 43
      errorCode InvalidMarkerError {}  = ErrorCode 49
      errorCode CoreNameLookupError {} = ErrorCode 50
      errorCode (PLCError e)           = errorCode e
      errorCode (PIRError e)           = errorCode e

instance (PLC.GShow uni, PLC.Closed uni, uni `PLC.Everywhere` PLC.PrettyConst, PP.Pretty fun, PP.Pretty a) =>
            PP.Pretty (Error uni fun a) where
    pretty = PLC.prettyPlcClassicDebug

instance uni1 ~ uni2 => PLC.AsTypeError (CompileError uni1 fun) (PIR.Term PIR.TyName PIR.Name uni2 fun ()) uni2 fun (PIR.Provenance ()) where
    _TypeError = _NoContext . _PIRError . PIR._TypeError

instance uni1 ~ uni2 => PIR.AsTypeErrorExt (CompileError uni1 fun) uni2 (PIR.Provenance ()) where
    _TypeErrorExt = _NoContext . _PIRError . PIR._TypeErrorExt

instance uni1 ~ uni2 => PLC.AsNormCheckError (CompileError uni1 fun) PLC.TyName PLC.Name uni2 fun () where
    _NormCheckError = _NoContext . _PLCError . PLC._NormCheckError

instance PLC.AsUniqueError (CompileError uni fun) () where
    _UniqueError = _NoContext . _PLCError . PLC._UniqueError

instance uni1 ~ uni2 => PIR.AsError (CompileError uni1 fun) uni2 fun (PIR.Provenance ()) where
    _Error = _NoContext . _PIRError

instance (PLC.GShow uni, PLC.Closed uni, uni `PLC.Everywhere` PLC.PrettyConst, PP.Pretty fun, PP.Pretty a) =>
            PLC.PrettyBy PLC.PrettyConfigPlc (Error uni fun a) where
    prettyBy config = \case
        PLCError e -> PP.vsep [ "Error from the PLC compiler:", PLC.prettyBy config e ]
        PIRError e -> PP.vsep [ "Error from the PIR compiler:", PLC.prettyBy config e ]
        CompilationError e -> "Unexpected error during compilation, please report this to the Plutus team:" PP.<+> PP.pretty e
        UnsupportedError e -> "Unsupported feature:" PP.<+> PP.pretty e
        FreeVariableError e -> "Reference to a name which is not a local, a builtin, or an external INLINABLE function:" PP.<+> PP.pretty e
        InvalidMarkerError e -> "Found invalid marker, not applied correctly in expression" PP.<+> PP.pretty e
        CoreNameLookupError n -> "Unable to get Core name needed for the plugin to function: " PP.<+> PP.viaShow n
