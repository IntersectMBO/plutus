{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusTx.Ual.Error
  ( UalError (..)
  , renderUalError
  ) where

import Prelude

import Data.Text (Text)
import Data.Text qualified as Text

-- | Everything that can go wrong in any UAL phase, with a source line where known.
data UalError
  = -- | Line of the opening @{\-\@@ that was never closed.
    UnterminatedBlock Int
  | -- | Line, and the unrecognised keyword that followed @{\-\@@.
    UnknownBlockKind Int Text
  | -- | Line, and what the parser expected.
    MalformedBlock Int Text
  | -- | The @ONCHAIN@ name, and the reason it could not be resolved.
    UnresolvedOnchainName Text Text
  | -- | The @ONCHAIN@ name, the arity UAL declares, the arity the Haskell type has.
    ArityMismatch Text Int Int
  | -- | The @ONCHAIN@ name, the version UAL declares, the preamble's version.
    VersionMismatch Text Text Text
  | -- | An @ONCHAIN@ name with no blueprint validator carrying the matching id.
    NoValidatorForOnchain Text
  | -- | A validator carrying @arguments@ or @budget@ with no @ONCHAIN@ block.
    OrphanValidatorArguments Text
  | -- | A validator id that occurs more than once in the contract.
    DuplicateValidatorId Text
  | -- | A property id that occurs more than once in the document.
    DuplicatePropertyId Text
  | -- | A property, and a @uses@ entry naming no existing fragment.
    UnknownFragment Text Text
  | -- | The fragment ids taking part in an import cycle.
    FragmentCycle [Text]
  | {-| No module declared a @PROPERTY@ block, so the assurance document would
    carry an empty @properties@ array. -}
    NoProperties
  {- Ord is derived only so that a phase collecting several errors can sort them
  into a stable report order. That order is the constructor order above and means
  nothing beyond determinism: it is not a severity ranking. -}
  deriving stock (Eq, Ord, Show)

renderUalError :: UalError -> Text
renderUalError = \case
  UnterminatedBlock l ->
    atLine l "unterminated '{-@' block: no '@-}' found"
  UnknownBlockKind l kw ->
    atLine l $
      "unknown UAL block kind "
        <> squote kw
        <> "; expected one of ONCHAIN, PREDICATE, PROPERTY, UPLC_DATA"
  MalformedBlock l what ->
    atLine l $ "malformed UAL block: " <> what
  UnresolvedOnchainName n why ->
    "ONCHAIN " <> squote n <> ": " <> why
  ArityMismatch n declared actual ->
    "ONCHAIN "
      <> squote n
      <> ": signature declares "
      <> tshow declared
      <> " argument(s) but the Haskell type has "
      <> tshow actual
  VersionMismatch n declared preamble ->
    "ONCHAIN "
      <> squote n
      <> ": declares version "
      <> declared
      <> " but the blueprint preamble says "
      <> preamble
  NoValidatorForOnchain n ->
    "ONCHAIN " <> squote n <> ": no validator in the blueprint has this id"
  OrphanValidatorArguments vid ->
    "validator " <> squote vid <> " carries arguments/budget but has no ONCHAIN block"
  DuplicateValidatorId vid ->
    "duplicate validator id " <> squote vid
  DuplicatePropertyId pid ->
    "duplicate property id " <> squote pid
  UnknownFragment pid frag ->
    "property " <> squote pid <> " uses unknown fragment " <> squote frag
  FragmentCycle ids ->
    "cycle in fragment imports: " <> Text.intercalate " -> " ids
  NoProperties ->
    "no PROPERTY blocks: an assurance document must declare at least one property"
  where
    atLine l msg = "line " <> tshow l <> ": " <> msg
    squote t = "'" <> t <> "'"
    tshow :: Show a => a -> Text
    tshow = Text.pack . show
