{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TemplateHaskell        #-}
module Language.PlutusTx.Compiler.Error (
    ConvError
    , Error (..)
    , WithContext (..)
    , withContext
    , withContextM
    , throwPlain
    , stripContext) where

import qualified Language.PlutusIR.Compiler as PIR

import qualified Language.PlutusCore        as PLC
import qualified Language.PlutusCore.Pretty as PLC

import           Control.Lens
import           Control.Monad.Except

import qualified Data.Text                  as T
import qualified Data.Text.Prettyprint.Doc  as PP
import           Data.Typeable

-- | An error with some (nested) context.
data WithContext c e = NoContext e | WithContextC c (WithContext c e)
    deriving Functor
makeClassyPrisms ''WithContext

type ConvError = WithContext T.Text (Error ())

withContext :: (MonadError (WithContext c e) m) => c -> m a -> m a
withContext c act = catchError act $ \err -> throwError (WithContextC c err)

withContextM :: (MonadError (WithContext c e) m) => m c -> m a -> m a
withContextM mc act = do
    c <- mc
    catchError act $ \err -> throwError (WithContextC c err)

throwPlain :: MonadError (WithContext c e) m => e -> m a
throwPlain = throwError . NoContext

stripContext :: WithContext c e -> e
stripContext = \case
    NoContext e -> e
    WithContextC _ e -> stripContext e

instance (PP.Pretty c, PP.Pretty e) => PP.Pretty (WithContext c e) where
    pretty = \case
        NoContext e     -> "Error:" PP.<+> (PP.align $ PP.pretty e)
        WithContextC c e -> PP.vsep [
            PP.pretty e,
            "Context:" PP.<+> (PP.align $ PP.pretty c)
            ]

data Error a = PLCError (PLC.Error a)
             | PIRError (PIR.Error (PIR.Provenance a))
             | ConversionError T.Text
             | UnsupportedError T.Text
             | FreeVariableError T.Text
             | ValueRestrictionError T.Text
             deriving Typeable
makeClassyPrisms ''Error

instance (PP.Pretty a) => PP.Pretty (Error a) where
    pretty = PLC.prettyPlcClassicDebug

instance PLC.AsRenameError ConvError () where
    _RenameError = _NoContext . _PLCError . PLC._RenameError

instance PLC.AsTypeError ConvError () where
    _TypeError = _NoContext . _PLCError . PLC._TypeError

instance PIR.AsError ConvError (PIR.Provenance ()) where
    _Error = _NoContext . _PIRError

instance (PP.Pretty a) => PLC.PrettyBy PLC.PrettyConfigPlc (Error a) where
    prettyBy config = \case
        PLCError e -> PLC.prettyBy config e
        PIRError e -> PLC.prettyBy config e
        ConversionError e -> "Error during conversion:" PP.<+> PP.pretty e
        UnsupportedError e -> "Unsupported:" PP.<+> PP.pretty e
        FreeVariableError e -> "Used but not defined in the current conversion:" PP.<+> PP.pretty e
        ValueRestrictionError e -> "Violation of the value restriction:" PP.<+> PP.pretty e
