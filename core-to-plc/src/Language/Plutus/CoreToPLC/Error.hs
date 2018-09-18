{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Plutus.CoreToPLC.Error (
    Error (..)
    , WithContext (..)
    , withContext
    , withContextM
    , mustBeReplaced) where

import qualified Language.PlutusCore       as PLC

import           Control.Monad.Except
import qualified Data.Text                 as T
import qualified Data.Text.Prettyprint.Doc as PP
import           Data.Typeable

-- | An error with some (nested) context.
data WithContext c e = NoContext e | WithContext c (WithContext c e)
    deriving Functor

withContext :: (MonadError (WithContext c e) m) => c -> m a -> m a
withContext c act = catchError act $ \err -> throwError (WithContext c err)

withContextM :: (MonadError (WithContext c e) m) => m c -> m a -> m a
withContextM mc act = do
    c <- mc
    catchError act $ \err -> throwError (WithContext c err)

instance (PP.Pretty c, PP.Pretty e) => PP.Pretty (WithContext c e) where
    pretty = \case
        NoContext e     -> "Error:" PP.<+> (PP.align $ PP.pretty e)
        WithContext c e -> PP.vsep [
            PP.pretty e,
            "Context:" PP.<+> (PP.align $ PP.pretty c)
            ]

data Error a = PLCError (PLC.Error a)
             | ConversionError T.Text
             | UnsupportedError T.Text
             | FreeVariableError T.Text
             deriving Typeable

instance (PLC.PrettyCfg a) => PP.Pretty (Error a) where
    pretty = PLC.prettyCfg PLC.debugCfg

instance (PLC.PrettyCfg a) => PLC.PrettyCfg (Error a) where
    prettyCfg cfg = \case
        PLCError e -> PLC.prettyCfg cfg e
        ConversionError e -> "Error during conversion:" PP.<+> PP.pretty e
        UnsupportedError e -> "Unsupported:" PP.<+> PP.pretty e
        FreeVariableError e -> "Used but not defined in the current conversion:" PP.<+> PP.pretty e

mustBeReplaced :: a
mustBeReplaced = error "This must be replaced by the core-to-plc plugin during compilation"
