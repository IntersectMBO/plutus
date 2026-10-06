{-# LANGUAGE OverloadedStrings #-}

module PlutusTx.Assurance.Build
  ( buildAssurance
  , ualLanguageKey
  ) where

import Prelude

import Data.List (nub, sort)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import PlutusTx.Assurance.Document
import PlutusTx.Ual.Error (UalError (..))
import PlutusTx.Ual.Syntax
  ( ModuleUal (..)
  , OnchainDecl (..)
  , PropertyDecl (..)
  , UalModuleName (..)
  )

-- | The @languages@ registry key this producer uses.
ualLanguageKey :: Text
ualLanguageKey = "ual"

{-| Assemble an assurance document from the UAL of every annotated module.

One fragment per module that has at least one @PREDICATE@ block, carrying that
module's predicate bodies stripped of surrounding whitespace and joined in
source order, because UAL lets a later block use definitions an earlier one
introduced. A fragment's @imports@ are that
module's imports restricted to the modules that also produced a fragment: the
raw import list names everything the module imports, and only a pass that sees
every module at once can tell which of those are fragments.

Properties carry no evidence records: this runs at build time, before any proof.
The CIP names that state explicitly — a property with no evidence is "a stated,
unverified claim … a machine-readable specification target".

Properties use explicit ONCHAIN scopes when present. The default validator is
only a shorthand for a single-target build; multi-target builds must say which
compiled programs each property constrains. Imported predicates remain reachable
through modules which have no predicate block of their own.

Scopes are non-empty and use explicit targets or the single-target default.
An empty property list returns 'NoProperties'; an empty authors list returns
'EmptyAssuranceAuthors'.

Every check below runs on every input, so one call reports duplicate property
ids, an import cycle and an empty property list together rather than stopping at
the first. Only one cycle is reported, however many the fragments contain. -}
buildAssurance
  :: AssurancePreamble
  -> BlueprintRef
  -> Text
  -- ^ The default validator id for a single-target build.
  -> [ModuleUal]
  -> Either [UalError] AssuranceDocument
buildAssurance preamble ref defaultValidator modules =
  case sort
    (dupPropertyErrors <> moduleErrors <> scopeErrors <> authorErrors <> cycleErrors <> noPropertyErrors) of
    [] ->
      Right
        MkAssuranceDocument
          { assurancePreamble = preamble
          , assuranceBlueprint = ref
          , assuranceLanguages = [(ualLanguageKey, ualRegistryEntry)]
          , assuranceTools = []
          , assuranceFormalFragments = fragments
          , assuranceProperties = properties
          }
    errs -> Left errs
  where
    nameOf (UalModuleName n) = n
    knownValidators = nub [onchainName d | m <- modules, d <- ualOnchain m]
    scopeOf p = if null (propertyScope p) then [defaultValidator] else propertyScope p
    scopeErrors =
      concat
        [ [ InvalidPropertyScope (propertyName p) "multiple ONCHAIN targets require an explicit [scope: ...]"
          | null (propertyScope p)
          , length knownValidators > 1
          ]
            <> [InvalidPropertyScope (propertyName p) "validator ids must be nonempty" | any Text.null (scopeOf p)]
            <> [ InvalidPropertyScope (propertyName p) ("unknown ONCHAIN id: " <> v)
               | v <- scopeOf p
               , not (null knownValidators)
               , v `notElem` knownValidators
               ]
        | m <- modules
        , p <- ualProperties m
        ]
    authorErrors = [EmptyAssuranceAuthors | null (assuranceAuthors preamble)]
    moduleErrors =
      [ DuplicateModule n
      | (n, count) <-
          Map.toList
            (Map.fromListWith (+) [(nameOf (ualModuleName m), 1 :: Int) | m <- modules])
      , count > 1
      ]

    -- Preserve imports through modules which have no predicates of their own.
    reachableFragments seen n
      | n `elem` seen = []
      | Set.member n fragmentIds = [n]
      | otherwise = case [m | m <- modules, nameOf (ualModuleName m) == n] of
          m : _ -> nub (concatMap (reachableFragments (n : seen) . nameOf) (ualModuleImports m))
          [] -> []
    importsOf m = nub (concatMap (reachableFragments [] . nameOf) (ualModuleImports m))

    fragmentModules :: [ModuleUal]
    fragmentModules = [m | m <- modules, not (null (ualPredicates m))]

    fragmentIds :: Set Text
    fragmentIds = Set.fromList (nameOf . ualModuleName <$> fragmentModules)

    fragments =
      [ MkFormalFragment
          { fragmentId = nameOf (ualModuleName m)
          , fragmentLanguage = ualLanguageKey
          , fragmentImports =
              importsOf m
          , fragmentSource = Text.intercalate "\n\n" (Text.strip <$> ualPredicates m)
          }
      | m <- fragmentModules
      ]

    properties =
      [ MkProperty
          { propertyIdent = propertyName p
          , propertyTitle = Nothing
          , propertyValidators = scopeOf p
          , propertyStatement =
              MkStatement
                { statementText = propertyText p
                , statementFormal =
                    Just
                      MkFormalStatement
                        { formalLanguage = ualLanguageKey
                        , formalUses = if Set.member mname fragmentIds then [mname] else importsOf m
                        , formalSource = propertyBody p
                        }
                }
          }
      | m <- modules
      , let mname = nameOf (ualModuleName m)
      , p <- ualProperties m
      ]

    {- The meta-schema marks @properties@ both required and @minItems: 1@, so an
    empty list is not a degenerate document but an invalid one. Refusing here
    rather than in 'PlutusTx.Assurance.Write.encodeAssurance' keeps the
    invariant with the producer that can explain it, and matches the two checks
    below, which also reject inputs only because the document they would
    produce is invalid. -}
    noPropertyErrors = [NoProperties | null properties]

    dupPropertyErrors =
      [ DuplicatePropertyId pid
      | (pid, n) <-
          Map.toList
            (Map.fromListWith (+) [(propertyName p, 1 :: Int) | m <- modules, p <- ualProperties m])
      , n > 1
      ]

    -- One cycle, if there is one, with its nodes in a stable order.
    cycleErrors = case findCycle edges of
      Nothing -> []
      Just c -> [FragmentCycle (sort c)]

    edges = Map.fromList [(fragmentId f, fragmentImports f) | f <- fragments]

ualRegistryEntry :: RegistryEntry
ualRegistryEntry =
  MkRegistryEntry
    { registryName = "Universal Annotation Language"
    , registryVersion = "0.5"
    , registryUri = Just "https://github.com/input-output-hk/UniversalAnnotationLanguage"
    , registryDescription = Just "Property specification language used by Blaster."
    }

{-| The first cycle found in a dependency graph, by depth-first search with a
path stack; 'Nothing' when there is none. Each node of the cycle appears once,
in the order the search reached it. A graph with several cycles yields whichever
one the search meets first, which for a fixed graph is always the same. -}
findCycle :: Map.Map Text [Text] -> Maybe [Text]
findCycle g = go (Map.keys g) Set.empty
  where
    go [] _ = Nothing
    go (n : ns) done
      | Set.member n done = go ns done
      | otherwise = case visit n [] done of
          Left cyc -> Just cyc
          Right done' -> go ns done'

    {- 'path' holds the ancestors of 'n', most recent first, and nothing else:
    that is why a node reached by two distinct paths -- a diamond -- is not
    taken for a cycle, since it is not its own ancestor. It never repeats a
    node, because the first guard ends the descent as soon as one would, so the
    stack is bounded by the number of nodes and the search terminates.

    'done' holds the nodes whose whole subtree has been explored without a
    cycle. It only avoids re-exploring a shared subtree, and cannot mask a
    cycle: a node enters it when its own call returns, by which time it is off
    the path, so no node is ever both in 'done' and on the current path. -}
    visit n path done
      | n `elem` path = Left (dropWhile (/= n) (reverse path))
      | Set.member n done = Right done
      | otherwise =
          case foldl step (Right done) (Map.findWithDefault [] n g) of
            Left cyc -> Left cyc
            Right done' -> Right (Set.insert n done')
      where
        step (Left cyc) _ = Left cyc
        step (Right d) m = visit m (n : path) d
