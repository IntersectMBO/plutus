{-# LANGUAGE OverloadedStrings #-}
module Language.PlutusIR.Compiler.Names (safeFreshName, safeFreshTyName) where

import           PlutusPrelude             (strToBs)

import qualified Language.PlutusCore       as PLC
import           Language.PlutusCore.Quote

import           Data.Char
import           Data.List
import qualified Data.Text                 as T

{- Note [PLC names]
We convert names from other kinds of names quite frequently, but PLC admits a much
smaller set of valid identifiers. We compromise by mangling the identifier, but
in the long run it would be nice to have a more principled encoding so we can
support unicode identifiers as well.
-}

replacements :: [(T.Text, T.Text)]
replacements = [
    -- this helps with module prefixes
    (".", "_")
    ]

typeReplacements :: [(T.Text, T.Text)]
typeReplacements = replacements ++ [
    ("[]", "List")
    , ("()", "Unit")
    , ("(,)", "Tuple2")
    , ("(,,)", "Tuple3")
    , ("(,,,)", "Tuple4")
    , ("(,,,,)", "Tuple5")
    ]

termReplacements :: [(T.Text, T.Text)]
termReplacements = replacements ++ [
    (":", "Cons")
    , ("[]", "Nil")
    , ("()", "Unit")
    , ("(,)", "Tuple2")
    , ("(,,)", "Tuple3")
    , ("(,,,)", "Tuple4")
    , ("(,,,,)", "Tuple5")
    ]

data NameKind = TypeName | TermName

safeName :: NameKind -> String -> String
safeName kind s =
    let
        t = T.pack s
        -- replace some special cases
        toReplace = case kind of
            TypeName -> typeReplacements
            TermName -> termReplacements
        replaced = foldl' (\acc (old, new) -> T.replace old new acc) t toReplace
        -- strip out disallowed characters
        stripped = T.filter (\c -> isLetter c || isDigit c || c == '_' || c == '`') replaced
        -- can't start with these
        dropped = T.dropWhile (\c -> c == '_' || c == '`') stripped
        -- empty name, just put something to mark that
        nonEmpty = if T.null dropped then "bad_name" else dropped
    in T.unpack nonEmpty

safeFreshName :: MonadQuote m => a -> String -> m (PLC.Name a)
safeFreshName ann s = liftQuote $ freshName ann $ strToBs $ safeName TermName s

safeFreshTyName :: MonadQuote m => a -> String -> m (PLC.TyName a)
safeFreshTyName ann s = liftQuote $ freshTyName ann $ strToBs $ safeName TypeName s
