{-# LANGUAGE RecordWildCards #-}

module PlutusTx.Ual.Resolve
  ( attachUal
  , onchainIdOf
  ) where

import Prelude

import Data.List (sort)
import Data.Map.Strict qualified as Map
import Data.Maybe (isJust)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import PlutusTx.Blueprint.Contract (ContractBlueprint (..))
import PlutusTx.Blueprint.PlutusVersion (PlutusVersion)
import PlutusTx.Blueprint.Preamble (Preamble (..))
import PlutusTx.Blueprint.Schema (Schema (SchemaDefinitionRef))
import PlutusTx.Blueprint.Validator (AppliedArgument (..), ValidatorBlueprint (..))
import PlutusTx.Ual.Error (UalError (..))
import PlutusTx.Ual.Syntax
  ( ModuleUal (..)
  , OnchainDecl (..)
  , OnchainKind (..)
  , ResolvedArgument (..)
  )

{-| The blueprint validator id an @ONCHAIN@ block claims. Identity, so the id is
readable straight off the annotation. The Template Haskell helper that derives a
validator id, @PlutusTx.Ual.TH.ualIdFor@, must agree with this. -}
onchainIdOf :: OnchainDecl -> Text
onchainIdOf = onchainName

{-| Attach the UAL interface facts to a blueprint: fill @arguments@ and @budget@
on every validator whose 'validatorId' matches an @ONCHAIN@ name.

Every check below is run on every input, so one call reports all the problems of
the kinds it checks rather than stopping at the first. It does not check anything
else: refined argument schemas remain the producer's responsibility, but
duplicate ONCHAIN names and unresolved argument lists are rejected. -}
attachUal :: [ModuleUal] -> ContractBlueprint -> Either [UalError] ContractBlueprint
attachUal modules MkContractBlueprint {..} =
  case sort
    ( dupIdErrors
        <> duplicateOnchainErrors
        <> unresolvedErrors
        <> versionErrors
        <> missingErrors
        <> orphanErrors
    ) of
    [] -> Right MkContractBlueprint {contractValidators = Set.map fill contractValidators, ..}
    errs -> Left errs
  where
    preambleVersion' = preamblePlutusVersion contractPreamble

    -- Duplicate names are diagnosed before the map is used.
    decls :: Map.Map Text OnchainDecl
    decls = Map.fromList [(onchainIdOf d, d) | m <- modules, d <- ualOnchain m, onchainKind d == Script]

    duplicateOnchainErrors =
      [ DuplicateOnchain n
      | (n, count) <-
          Map.toList
            ( Map.fromListWith
                (+)
                [(onchainName d, 1 :: Int) | m <- modules, d <- ualOnchain m, onchainKind d == Script]
            )
      , count > 1
      ]

    unresolvedErrors =
      [ UnresolvedArguments (onchainName d)
      | d <- Map.elems decls
      , length (onchainResolvedArgs d) /= length (onchainArgs d)
      ]

    validatorIds :: [Text]
    validatorIds = [vid | v <- Set.toList contractValidators, Just vid <- [validatorId v]]

    idSet = Set.fromList validatorIds

    dupIdErrors =
      [ DuplicateValidatorId vid
      | (vid, n) <- Map.toList (Map.fromListWith (+) [(v, 1 :: Int) | v <- validatorIds])
      , n > 1
      ]

    versionErrors =
      [ VersionMismatch (onchainIdOf d) (renderVersion v) (renderVersion preambleVersion')
      | d <- Map.elems decls
      , Just v <- [onchainVersion d]
      , v /= preambleVersion'
      ]

    -- An ONCHAIN block naming no validator.
    missingErrors =
      [NoValidatorForOnchain vid | vid <- Map.keys decls, not (Set.member vid idSet)]

    {- A validator that already carries arguments or a budget but has no ONCHAIN
    block. This catches hand-written interface facts that UAL would silently
    fail to keep in sync. -}
    orphanErrors =
      [ OrphanValidatorArguments vid
      | v <- Set.toList contractValidators
      , Just vid <- [validatorId v]
      , not (Map.member vid decls)
      , not (null (validatorArguments v)) || isJust (validatorBudget v)
      ]

    {- No type signature: 'referencedTypes' is bound by the pattern match on the
    existential 'MkContractBlueprint', so 'fill''s type cannot be written down
    here. Never changes 'validatorTitle', the first field of the derived 'Ord',
    so the 'Set.map' above cannot collapse two distinct validators into one. -}
    fill v = case validatorId v >>= \vid -> Map.lookup vid decls of
      Nothing -> v
      Just d ->
        v
          { validatorArguments = toApplied <$> onchainResolvedArgs d
          , validatorBudget = onchainBudget d
          }

    {- Reads 'onchainResolvedArgs', not 'onchainArgs': only a 'DefinitionId'
    builds a 'SchemaDefinitionRef', and the parser has type names, not types. A
    declaration that never went through the Template Haskell splice therefore
    contributes no arguments at all, and the encoder omits the key. -}
    toApplied r =
      MkAppliedArgument
        { appliedArgumentEncoding = resolvedEncoding r
        , appliedArgumentSchema = SchemaDefinitionRef (resolvedDefinitionId r)
        }

renderVersion :: PlutusVersion -> Text
renderVersion = Text.pack . show
