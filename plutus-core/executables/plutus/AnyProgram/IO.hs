{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
module AnyProgram.IO
    ( readProgram
    , writeProgram
    ) where

import Common
import Types
import GetOpt
import AnyProgram.With
import AnyProgram.Parse

import PlutusCore.Default
import PlutusIR.Error qualified as PIR
import PlutusPrelude
import Data.ByteString qualified as BS
import Flat
import System.IO
import Data.Text.Encoding qualified as T
import PlutusCore.Pretty qualified as PP
import Prettyprinter
import Prettyprinter.Render.Text
import Control.Monad

readProgram :: SLang s -> File s -> IO (FromLang s)
readProgram sngS fileS = do
    bs <- readFileName (fileS^.fName)
    case fileS^.fType.fFormat of
        Text ->
            case parseProgram @(PIR.Error DefaultUni DefaultFun _) sngS $ T.decodeUtf8Lenient bs of
                Left err -> withPrettyA (_sann sngS) $ failE $ show err
                Right res -> pure res
        Flat_ -> withFlatL sngS $
            case unflat bs of
                Left err -> failE $ show err
                Right res -> pure res
        _ -> failE "not implemented yet"

writeProgram :: (?opts :: Opts)
             => SLang s -> File s -> FromLang s -> IO ()
writeProgram sng file ast
    | _noCode ?opts = pure ()
    | otherwise = do
          when (_verbosity ?opts == VFull) $
              printE $ show $ "Outputting" <+> pretty file
          case file^.fType.fFormat of
              Flat_ -> writeFileName (file^.fName) $ withFlatL sng $ flat ast
              Text  -> writeFileName (file^.fName)
                    $ T.encodeUtf8
                    $ renderStrict
                    $ layoutPretty defaultLayoutOptions
                    $ withPrettyPlcL sng
                    $ prettyWithStyle (_prettyStyle ?opts) ast
              _ -> failE "not implemented yet"

prettyWithStyle :: PP.PrettyPlc (FromLang s)
                => PrettyStyle -> FromLang s -> Doc ann
prettyWithStyle = \case
        Classic       -> PP.prettyPlcClassicDef
        ClassicDebug  -> PP.prettyPlcClassicDebug
        Readable      -> PP.prettyPlcReadableDef
        ReadableDebug -> PP.prettyPlcReadableDebug
        None -> error "not implemented yet"

readFileName :: FileName -> IO BS.ByteString
readFileName = \case
    StdOut -> failE "should not happen"
    -- TODO: it needs some restructuring above on readProgram, because the example should return an ast instead of bytestring
    Example -> failE "not implemented yet"
    StdIn -> BS.hGetContents stdin
    AbsolutePath fp -> BS.readFile fp

writeFileName :: FileName -> BS.ByteString -> IO ()
writeFileName fn bs = case fn of
    StdIn -> failE "should not happen"
    Example -> failE "should not happen"
    StdOut -> BS.hPutStr stdout bs
    AbsolutePath fp -> BS.writeFile fp bs
