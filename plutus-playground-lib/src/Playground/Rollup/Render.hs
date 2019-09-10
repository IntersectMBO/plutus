{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Playground.Rollup.Render
    ( showBlockchain
    ) where

import           Control.Lens                          (preview, _2, _Just)
import           Control.Lens.Combinators              (itraverse)
import           Control.Monad.Except                  (MonadError, throwError)
import           Control.Monad.State                   (StateT, evalStateT, get, gets)
import           Crypto.Hash                           (Digest, SHA256)
import qualified Data.Aeson.Extras                     as JSON
import qualified Data.ByteString.Lazy.Char8            as C8
import           Data.List                             (find, intersperse)
import           Data.Map                              (Map)
import qualified Data.Map                              as Map
import           Data.Set                              (Set)
import qualified Data.Set                              as Set
import           Data.Text                             (Text)
import qualified Data.Text                             as Text
import           Data.Text.Prettyprint.Doc             (Doc, defaultLayoutOptions, fill, indent, layoutPretty, line,
                                                        parens, pretty, viaShow, vsep, (<+>))
import           Data.Text.Prettyprint.Doc.Render.Text (renderStrict)
import qualified Language.PlutusTx.AssocMap            as AssocMap
import           Ledger                                (DataScript, PubKey, Tx (Tx), TxId, TxOut, TxOutOf (TxOutOf),
                                                        TxOutType (PayToPubKey, PayToScript), Value, getPubKey, getTxId,
                                                        txFee, txForge, txOutType, txOutValue, txOutputs)
import           Ledger.Ada                            (Ada (Lovelace))
import qualified Ledger.Ada                            as Ada
import           Ledger.Value                          (CurrencySymbol (CurrencySymbol), TokenName (TokenName),
                                                        getValue)
import qualified Ledger.Value                          as Value
import           Playground.Rollup                     (doAnnotateBlockchain)
import           Playground.Types                      (AnnotatedTx (AnnotatedTx), EvaluationResult,
                                                        SequenceId (SequenceId, slotIndex, txIndex), balances,
                                                        dereferencedInputs, resultBlockchain, tx, txId, walletKeys)
import           Wallet.Emulator.Types                 (Wallet (Wallet))

showBlockchain :: EvaluationResult -> Either Text Text
showBlockchain evalutionResult =
    flip evalStateT evalutionResult $ do
        evaluationResult <- get
        annotatedBlockchain <-
            doAnnotateBlockchain (resultBlockchain evaluationResult)
        doc <- render $ reverse annotatedBlockchain
        pure . renderStrict . layoutPretty defaultLayoutOptions $ doc

------------------------------------------------------------
class Render a where
    render :: a -> StateT EvaluationResult (Either Text) (Doc ann)

instance Render [[AnnotatedTx]] where
    render = numbered "====" "Slot"

instance Render [AnnotatedTx] where
    render = numbered "----" "Tx"

instance Render AnnotatedTx where
    render AnnotatedTx { txId
                       , tx = Tx {txOutputs, txForge, txFee}
                       , dereferencedInputs
                       , balances
                       } =
        vsep <$>
        sequence
            [ heading "TxId:" txId
            , heading "Fee:" txFee
            , heading "Forge:" txForge
            , pure "Inputs:"
            , indented dereferencedInputs
            , pure line
            , pure "Outputs:"
            , indented txOutputs
            , pure line
            , pure "Balances Carried Forward:"
            , indented balances
            ]
      where
        heading t x = do
            r <- indented x
            pure $ fill 10 t <> r

instance Render SequenceId where
    render SequenceId {..} =
        pure $
        "Slot #" <> viaShow slotIndex <> "," <+>
        "Transaction #" <> viaShow txIndex

instance Render CurrencySymbol where
    render (CurrencySymbol "")    = pure "Ada"
    render (CurrencySymbol other) = pure $ pretty $ C8.unpack other

instance Render TokenName where
    render (TokenName "") = pure "Lovelace"
    render t              = pure $ pretty $ Value.toString t

instance Render Value where
    render value = render (getValue value)

instance (Render k, Render v) => Render (AssocMap.Map k v) where
    render m
        | null (AssocMap.toList m) = pure "-"
        | otherwise =
            vsep <$>
            traverse
                (\(k, v) -> do
                     rk <- render k
                     rv <- render v
                     pure $ fill 8 (rk <> ":") <> indent 2 rv)
                (AssocMap.toList m)

instance Render (Map TxOutType Value) where
    render xs
        | Map.null xs = pure "-"
        | otherwise = do
            entries <-
                traverse
                    (\(k, v) -> do
                         rk <- render k
                         rv <- render v
                         pure $ vsep [rk, rv])
                    (Map.toList xs)
            pure $ vsep $ intersperse mempty entries

instance Render Text where
    render = pure . pretty

instance Render String where
    render = pure . pretty

instance Render Integer where
    render = pure . pretty

instance Render Wallet where
    render (Wallet n) = pure $ "Wallet" <+> viaShow n

instance Render TxOutType where
    render (PayToScript dataScript) = render dataScript
    render (PayToPubKey pubKey) = do
        walletKeys <- gets walletKeys
        wallet <- lookupWallet pubKey walletKeys
        w <- render wallet
        p <- render pubKey
        pure $ w <+> parens p

instance Render Ada where
    render ada@(Lovelace l)
        | Ada.isZero ada = pure "-"
        | otherwise = pure $ "Ada" <+> pretty l

instance Render (Digest SHA256) where
    render = render . JSON.encodeSerialise

instance Render TxId where
    render t = pure $ viaShow (getTxId t)

instance Render PubKey where
    render = pure . viaShow . getPubKey

instance Render DataScript where
    render = pure . viaShow

instance Render a => Render (Set a) where
    render xs = vsep <$> traverse render (Set.toList xs)

instance Render [TxOut] where
    render = numbered "__" "Entry"

instance Render TxOut where
    render TxOutOf {txOutValue, txOutType} =
        vsep <$>
        sequence [heading "Type:" txOutType, heading "Value:" txOutValue]
      where
        heading t x = do
            r <- render x
            pure $ fill 10 t <> r

------------------------------------------------------------
indented :: Render a => a -> StateT EvaluationResult (Either Text) (Doc ann)
indented x = indent 2 <$> render x

numbered ::
       Render a
    => Doc ann
    -> Doc ann
    -> [a]
    -> StateT EvaluationResult (Either Text) (Doc ann)
numbered separator title xs =
    vsep . intersperse mempty <$> itraverse numberedEntry xs
  where
    numberedEntry index x = do
        v <- render x
        pure $ vsep [separator <+> title <+> viaShow index <+> separator, v]

------------------------------------------------------------
lookupWallet ::
       (MonadError Text m, Foldable t)
    => PubKey
    -> t (PubKey, Wallet)
    -> m Wallet
lookupWallet pubKey walletKeys = do
    let mWallet = preview (_Just . _2) (find ((==) pubKey . fst) walletKeys)
    case mWallet of
        Nothing ->
            throwError $
            Text.pack $ "Could not find referenced PubKey: " <> show pubKey
        Just wallet -> pure wallet
