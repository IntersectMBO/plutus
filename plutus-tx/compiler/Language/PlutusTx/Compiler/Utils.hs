{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.PlutusTx.Compiler.Utils where

import           Language.PlutusTx.Compiler.Error
import           Language.PlutusTx.Compiler.Types

import qualified GhcPlugins                       as GHC

import           Control.Monad.Except
import           Control.Monad.Reader

import qualified Data.Text                        as T

sdToTxt :: (MonadReader ConvertingContext m) => GHC.SDoc -> m T.Text
sdToTxt sd = do
  ConvertingContext { ccFlags=flags } <- ask
  pure $ T.pack $ GHC.showSDoc flags sd

throwSd :: (MonadError ConvError m, MonadReader ConvertingContext m) => (T.Text -> Error ()) -> GHC.SDoc -> m a
throwSd constr = (throwPlain . constr) <=< sdToTxt
