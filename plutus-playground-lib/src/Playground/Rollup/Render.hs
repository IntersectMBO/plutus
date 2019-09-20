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
import qualified Data.ByteString.Lazy                  as BSL
import           Data.Foldable                         (fold)
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
import qualified Language.PlutusTx.Builtins            as Builtins
import           Ledger                                (Address, PubKey, Tx (Tx), TxId, TxIn,
                                                        TxInOf (TxInOf, txInRef, txInType),
                                                        TxInType (ConsumePublicKeyAddress, ConsumeScriptAddress), TxOut,
                                                        TxOutOf (TxOutOf), TxOutRef,
                                                        TxOutRefOf (TxOutRefOf, txOutRefId, txOutRefIdx), Value,
                                                        getAddress, getPubKey, getTxId, txFee, txForge, txOutValue,
                                                        txOutputs)
import           Ledger.Ada                            (Ada (Lovelace))
import qualified Ledger.Ada                            as Ada
import           Ledger.Scripts                        (DataScript (getDataScript), Script,
                                                        ValidatorScript (getValidator))
import           Ledger.Value                          (CurrencySymbol (CurrencySymbol), TokenName (TokenName),
                                                        getValue)
import qualified Ledger.Value                          as Value
import           Playground.Rollup                     (doAnnotateBlockchain)
import           Playground.Types                      (AnnotatedTx (AnnotatedTx),
                                                        BeneficialOwner (OwnedByPubKey, OwnedByScript),
                                                        DereferencedInput (DereferencedInput, originalInput, refersTo),
                                                        EvaluationResult, SequenceId (SequenceId, slotIndex, txIndex),
                                                        balances, dereferencedInputs, resultBlockchain,
                                                        toBeneficialOwner, tx, txId, walletKeys)
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
    render blockchain =
        vsep . intersperse mempty . fold <$>
        itraverse
            (\slotIndex ->
                 itraverse
                     (\txIndex tx -> do
                          i <- render SequenceId {..}
                          v <- render tx
                          pure $ vsep ["====" <+> i <+> "====", v]))
            blockchain

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
            , indent 2 <$> numbered "----" "Input" dereferencedInputs
            , pure line
            , pure "Outputs:"
            , indent 2 <$> numbered "----" "Output" txOutputs
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
        "Slot #" <> viaShow slotIndex <> "," <+> "Tx #" <> viaShow txIndex

instance Render CurrencySymbol where
    render (CurrencySymbol "")    = pure "Ada"
    render (CurrencySymbol other) = render other

instance Render TokenName where
    render (TokenName "") = pure "Lovelace"
    render t              = pure $ pretty $ Value.toString t

instance Render Builtins.ByteString where
    render = pure . pretty . JSON.encodeByteString . BSL.toStrict

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

instance Render (Map BeneficialOwner Value) where
    render xs
        | Map.null xs = pure "-"
        | otherwise = do
            entries <-
                traverse
                    (\(k, v) -> do
                         rk <- render k
                         rv <- render v
                         pure $ vsep [rk, "Value:", indent 2 rv])
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

instance Render Address where
    render = render . getAddress

instance Render BeneficialOwner where
    render (OwnedByScript address) = ("Script:" <+>) <$> render address
    render (OwnedByPubKey pubKey) = do
        walletKeys <- gets walletKeys
        wallet <- lookupWallet pubKey walletKeys
        w <- render wallet
        p <- render pubKey
        pure $ p <+> parens w

instance Render Ada where
    render ada@(Lovelace l)
        | Ada.isZero ada = pure "-"
        | otherwise = pure $ "Ada" <+> pretty l

instance Render (Digest SHA256) where
    render = render . abbreviate 40 . JSON.encodeSerialise

instance Render TxId where
    render t = pure $ viaShow (getTxId t)

instance Render PubKey where
    render pubKey =
        pure $
        let v = Text.pack (show (getPubKey pubKey))
         in "PubKey:" <+> pretty (abbreviate 40 v)

instance Render Script where
    render script =
        pure $
        let v = JSON.encodeSerialise script
         in "Script:" <+> pretty (abbreviate 40 v)

instance Render ValidatorScript where
    render = render . getValidator

instance Render DataScript where
    render = render . getDataScript

instance Render a => Render (Set a) where
    render xs = vsep <$> traverse render (Set.toList xs)

instance Render DereferencedInput where
    render DereferencedInput {originalInput, refersTo} =
        vsep <$>
        sequence
            [render refersTo, pure "Source:", indent 2 <$> render originalInput]

instance Render TxIn where
    render TxInOf {txInRef, txInType} =
        vsep <$> sequence [render txInRef, render txInType]

instance Render TxInType where
    render (ConsumeScriptAddress validator _) = render validator
    render (ConsumePublicKeyAddress pubKey)   = render pubKey

instance Render TxOutRef where
    render TxOutRefOf {txOutRefId, txOutRefIdx} =
        vsep <$>
        sequence [heading "Tx:" txOutRefId, heading "Output #" txOutRefIdx]
      where
        heading t x = do
            r <- render x
            pure $ fill 8 t <> r

instance Render TxOut where
    render txOut@TxOutOf {txOutValue} =
        vsep <$>
        sequence
            [ mappend "Destination:" . indent 2 <$>
              render (toBeneficialOwner txOut)
            , pure "Value:"
            , indent 2 <$> render txOutValue
            ]

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

abbreviate :: Int -> Text -> Text
abbreviate n t =
    let prefix = Text.take n t
     in if prefix == t
            then t
            else prefix <> "..."
