{-# LANGUAGE TypeApplications #-}
module AnyProgram.Parse
    ( parseProgram
    ) where

import PlutusPrelude hiding ((%~))
import Types
import AnyProgram.Compile

import PlutusCore.Error as PLC
import PlutusIR.Error as PIR
import PlutusCore.Quote as PLC

import PlutusCore.Parser qualified as PLC
import PlutusIR.Parser qualified as PIR
import UntypedPlutusCore.Parser qualified as UPLC
import UntypedPlutusCore qualified as UPLC

import Data.Text qualified as T
import Data.Singletons.Decide
import Control.Monad.Except

-- | Given a singleton witness and two programs of that type witness, apply them together.
--
-- This could alternatively be achieved by
-- using a "Parsable" typeclass + withParsable hasomorphism
parseProgram :: ( PIR.AsError e uni fun (FromAnn (US_ann n))
               , AsParserErrorBundle e
               , MonadError e m)
             => SLang n -> T.Text -> m (FromLang n)
parseProgram s bs = PLC.runQuoteT $
    case _snaming s %~ SName of
        Proved Refl -> case _sann s of
            SSrcSpan_ ->
                -- TODO: deduplicate
                      case s of
                          SPir{} -> PIR.parseProgram bs
                          SPlc{} -> PLC.parseProgram bs
                          SUplc{} -> UPLC.UnrestrictedProgram <$> UPLC.parseProgram bs
                          SData{} -> error "FIXME: not implemented yet"
            SUnit ->
                      case s of
                          SPir{} -> toOutAnn SSrcSpan_ (_sann s) =<< PIR.parseProgram bs
                          SPlc{} -> void <$> PLC.parseProgram bs
                          SUplc{} -> void <$> UPLC.UnrestrictedProgram <$> UPLC.parseProgram bs
                          SData{} -> error "FIXME: not implemented yet"
        _ -> error "cannot parse non name"


