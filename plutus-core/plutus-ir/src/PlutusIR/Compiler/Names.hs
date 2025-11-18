{-# LANGUAGE OverloadedStrings #-}

module PlutusIR.Compiler.Names (safeFreshName, safeFreshTyName) where

import PlutusCore qualified as PLC
import PlutusCore.Name.Unique (isQuotedIdentifierChar)
import PlutusCore.Quote

import Data.List qualified as List
import Data.Text qualified as T

{- Note [PLC names]
We convert names from other kinds of names quite frequently, but PLC admits a much
smaller set of valid identifiers. We compromise by mangling the identifier, but
in the long run it would be nice to have a more principled encoding so we can
support unicode identifiers as well.
-}

typeReplacements :: [(T.Text, T.Text)]
typeReplacements =
  [ ("[]", "List")
  , ("()", "Unit")
  , ("(,)", "Tuple2")
  , ("(,,)", "Tuple3")
  , ("(,,,)", "Tuple4")
  , ("(,,,,)", "Tuple5")
  , ("(#,#)", "UTuple2")
  , ("(#,,#)", "UTuple3")
  , ("(#,,,#)", "UTuple4")
  , ("(#,,,,#)", "UTuple5")
  ]

termReplacements :: [(T.Text, T.Text)]
termReplacements =
  [ (":", "Cons")
  , ("[]", "Nil")
  , ("()", "Unit")
  , ("(,)", "Tuple2")
  , ("(,,)", "Tuple3")
  , ("(,,,)", "Tuple4")
  , ("(,,,,)", "Tuple5")
  , ("(#,#)", "UTuple2")
  , ("(#,,#)", "UTuple3")
  , ("(#,,,#)", "UTuple4")
  , ("(#,,,,#)", "UTuple5")
  ]

data NameKind = TypeName | TermName

safeName :: NameKind -> T.Text -> T.Text
safeName kind t =
  let
    -- replace some special cases
    toReplace = case kind of
      TypeName -> typeReplacements
      TermName -> termReplacements
    replaced = List.foldl' (\acc (old, new) -> T.replace old new acc) t toReplace
    -- strip out disallowed characters
    stripped = T.filter isQuotedIdentifierChar replaced
   in
    if T.null stripped then "bad_name" else stripped

safeFreshName :: MonadQuote m => T.Text -> m PLC.Name
safeFreshName s = liftQuote $ freshName $ safeName TermName s

safeFreshTyName :: MonadQuote m => T.Text -> m PLC.TyName
safeFreshTyName s = liftQuote $ freshTyName $ safeName TypeName s
