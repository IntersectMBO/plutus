{-# LANGUAGE TemplateHaskell #-}

module Language.Plutus.CoreToPLC.Primitives where

import qualified GhcPlugins                 as GHC

import qualified Language.PlutusCore        as PC

import qualified Language.Haskell.TH.Syntax as TH

import           GHC.Natural

import           Control.Monad

import           Data.ByteString
import qualified Data.Map                   as Map
import           Data.Maybe                 (catMaybes)

haskellIntSize :: Natural
haskellIntSize = 64

haskellBSSize :: Natural
haskellBSSize = 64

instSize :: Natural -> PC.Term tyname name () -> PC.Term tyname name ()
instSize n t = PC.TyInst () t (PC.TyInt () n)

appSize :: Natural -> PC.Type tyname () -> PC.Type tyname ()
appSize n t = PC.TyApp () t (PC.TyInt () n)

mkConstant :: PC.BuiltinName -> PC.Term tyname name ()
mkConstant n = PC.Constant () $ PC.BuiltinName () n

-- TODO: resizing primitives? better handling of sizes?

concatenate :: ByteString -> ByteString -> ByteString
concatenate = undefined

takeByteString :: Int -> ByteString -> ByteString
takeByteString = undefined

dropByteString :: Int -> ByteString -> ByteString
dropByteString = undefined

sha2_256 :: ByteString -> ByteString
sha2_256 = undefined

sha3_256 :: ByteString -> ByteString
sha3_256 = undefined

verifySignature :: ByteString -> ByteString -> ByteString -> Bool
verifySignature = undefined

equalsByteString :: ByteString -> ByteString -> Bool
equalsByteString = undefined

txhash :: ByteString
txhash = undefined

blocknum :: Int
blocknum = undefined

primitiveAssociations :: [(TH.Name, (PC.Term PC.TyName PC.Name ()))]
primitiveAssociations = [
    ('concatenate, instSize haskellIntSize $ mkConstant PC.Concatenate)
    , ('takeByteString, instSize haskellBSSize $ instSize haskellIntSize $ mkConstant PC.TakeByteString)
    , ('dropByteString, instSize haskellBSSize $ instSize haskellIntSize $ mkConstant PC.DropByteString)
    , ('sha2_256, instSize haskellBSSize $ mkConstant PC.SHA2)
    , ('sha3_256, instSize haskellBSSize $ mkConstant PC.SHA3)
    , ('verifySignature, instSize haskellBSSize $ instSize haskellBSSize $ instSize haskellBSSize $ mkConstant PC.VerifySignature)
    , ('equalsByteString, instSize haskellBSSize $ instSize haskellBSSize $ mkConstant PC.EqByteString)
    , ('txhash, mkConstant PC.TxHash)
    , ('blocknum, instSize haskellIntSize $ mkConstant PC.BlockNum)
    ]

makePrimitivesMap :: GHC.CoreM (Map.Map GHC.Name (PC.Term PC.TyName PC.Name ()))
makePrimitivesMap = do
    mapped <- forM primitiveAssociations $ \(name, term) -> do
        ghcNameMaybe <- GHC.thNameToGhcName name
        pure $ fmap (\ghcName -> (ghcName, term)) ghcNameMaybe
    pure $ Map.fromList (catMaybes mapped)
