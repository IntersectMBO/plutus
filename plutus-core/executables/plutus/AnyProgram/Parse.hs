module AnyProgram.Parse
  ( parseProgram
  ) where

import PlutusPrelude hiding ((%~))
import Types

import PlutusCore.Error as PLC
import PlutusCore.Quote as PLC

import PlutusCore.Parser qualified as PLC
import PlutusIR.Parser qualified as PIR
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Parser qualified as UPLC

import Control.Monad.Except
import Data.Singletons.Decide
import Data.Text qualified as T
import PlutusCore.Data

{-| Given a singleton witness and two programs of that type witness, apply them together.

This could alternatively be achieved by
using a "Parsable" typeclass + withL @Parsable hasomorphism -}
parseProgram
  :: MonadError ParserErrorBundle m
  => SLang n -> T.Text -> m (FromLang n)
parseProgram s txt = PLC.runQuoteT $
  case s of
    SData {} -> pure $ read @Data $ T.unpack txt
    _ -> case _snaming s %~ SName of
      Proved Refl -> case _sann s of
        STxSrcSpans -> error "Parsing TxSrcSpans is not available."
        SUnit ->
          case s of
            SPir {} -> void <$> PIR.parseProgram txt
            SPlc {} -> void <$> PLC.parseProgram txt
            SUplc {} -> UPLC.UnrestrictedProgram . void <$> UPLC.parseProgram txt
      -- SSrcSpan_ ->
      --       case s of
      --           SPir{} -> PIR.parseProgram txt
      --           SPlc{} -> PLC.parseProgram txt
      --           SUplc{} -> UPLC.UnrestrictedProgram <$> UPLC.parseProgram txt
      _ -> error "Parsing (named-)debruijn program is not available."
