{-# LANGUAGE ImplicitParams    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module AnyProgram.IO
    ( readProgram
    , writeProgram
    , prettyWithStyle
    ) where

import AnyProgram.Parse
import AnyProgram.With
import Common
import GetOpt
import PlutusCore.Default
import PlutusCore.Pretty qualified as PP
import PlutusPrelude hiding ((%~))
import Types

import Codec.Extras.SerialiseViaFlat
import Codec.Serialise (deserialiseOrFail, serialise)
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as BSL
import Data.Maybe
import Data.Singletons.Decide
import Data.Text.Encoding qualified as T
import PlutusCore.Flat
import Prettyprinter
import Prettyprinter.Render.Text
import System.IO

readProgram :: (?opts :: Opts)
            => SLang s -> File s -> IO (FromLang s)
readProgram sngS fileS =
    case fileS^.fName of
        Just (Example _eName) ->
            error "FIXME: Not implemented yet."
            -- case sngS of
            --     SPir SName SUnit ->
            --         case lookup eName termExamples of
            --             Just ast -> pure $ PIR.Program () undefined ast
            --             Nothing -> error $ "Couldn't find example with name " ++ eName
        _ -> case fileS^.fType.fFormat of
                Text -> do
                    bs <- readFileName (fromJust $ fileS^.fName)
                    case parseProgram sngS $ T.decodeUtf8Lenient bs of
                        Left err  -> failE $ show err
                        Right res -> pure res
                Flat_ -> withLang @Flat sngS $ do
                    bs <- readFileName (fromJust $ fileS^.fName)
                    case unflat bs of
                       Left err  -> failE $ show err
                       Right res -> pure res
                Cbor -> do
                    bs <- readFileName (fromJust $ fileS^.fName)
                    -- TODO: deduplicate
                    case sngS %~ SData of
                        Proved Refl ->
                            case deserialiseOrFail $ BSL.fromStrict bs of
                                   Left err  -> failE $ show err
                                   Right res -> pure res
                        _ ->  withLang @Flat sngS $
                            -- this is a cbor-embedded bytestring of the Flat encoding
                            -- so we use the SerialiseViaFlat newtype wrapper.
                            case deserialiseOrFail $ BSL.fromStrict bs of
                                   Left err                     -> failE $ show err
                                   Right (SerialiseViaFlat res) -> pure res
                Json -> error "FIXME: not implemented yet."

writeProgram :: (?opts :: Opts)
             => SLang s -> FromLang s -> File s -> AfterCompile -> IO ()
writeProgram sng ast file afterCompile =
    case file^.fName of
        Just fn -> do
            printED $ show $ "Outputting" <+> pretty file
            case file^.fType.fFormat of
                Flat_ -> writeFileName fn $ withLang @Flat sng $ flat ast
                Text  -> writeFileName fn
                    $ T.encodeUtf8
                    $ renderStrict
                    $ layoutPretty defaultLayoutOptions
                    $ withPrettyPlcL sng
                    $ prettyWithStyle (_prettyStyle ?opts) ast
                Cbor -> writeFileName fn $ BSL.toStrict $
                    case sng %~ SData of
                        Proved Refl -> serialise ast
                        _           -> withLang @Flat sng $ serialise (SerialiseViaFlat ast)
                Json -> error "FIXME: not implemented yet"
        _ -> case afterCompile of
                Exit -> printE
                       "Compilation succeeded, but no output file was written; use -o or --stdout."
                _ -> pure ()

prettyWithStyle :: PP.PrettyPlc a => PrettyStyle -> a -> Doc ann
prettyWithStyle = \case
        Classic       -> PP.prettyPlcClassic
        ClassicSimple  -> PP.prettyPlcClassicSimple
        Readable      -> PP.prettyPlcReadable
        ReadableSimple -> PP.prettyPlcReadableSimple

readFileName :: (?opts :: Opts)
             => FileName -> IO BS.ByteString
readFileName = \case
    StdOut          -> failE "should not happen"
    StdIn           -> BS.hGetContents stdin
    AbsolutePath fp -> BS.readFile fp
    -- TODO: it needs some restructuring in Types, Example is not a FileName and cannot be IO-read
    Example{}       -> failE "should not happen"

writeFileName :: (?opts :: Opts)
              => FileName -> BS.ByteString -> IO ()
writeFileName fn bs = case fn of
    StdIn           -> failE "should not happen"
    Example{}       -> failE "should not happen"
    StdOut          -> BS.hPutStr stdout bs
    AbsolutePath fp -> BS.writeFile fp bs
