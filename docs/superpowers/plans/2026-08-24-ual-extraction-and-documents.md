# UAL Extraction and Output Documents Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Let a Plinth author write UAL annotations in `{-@ … @-}` comments and have `gen-blueprint` emit a CIP-57 blueprint extended with applied-argument encodings plus an assurance document carrying the predicates and properties.

**Architecture:** A pure core (lexer → parser → `ModuleUal`) with no GHC dependency, a thin Template Haskell adapter (`$(ualModule)`) that reads the enclosing module's own source and resolves names via `reify`, and two pure assembly functions (`attachUal`, `buildAssurance`) that the author's `gen-blueprint` executable composes. All new code lives in `plutus-tx`, reusing `PlutusTx.Blueprint` types.

**Tech Stack:** Haskell (GHC 9.x), `text`, `aeson`, `template-haskell`, `tasty` + `tasty-hunit` + `tasty-hedgehog`, golden files via `Test.Tasty.Extras.goldenVsText` from `plutus-core:plutus-core-testlib`.

**Spec:** `docs/superpowers/specs/2026-08-24-ual-extended-blueprints-design.md`

---

## Orientation for the implementer

You are working in the `plutus` monorepo (IntersectMBO/plutus). Things you need to know that are not obvious:

- **Build and test — you MUST pass `--project-file=cabal.project.ual`.** This
  repo normally builds inside a nix devshell, and nix is not installed here. The
  root `cabal.project` lists `plutus-benchmark`, `plutus-metatheory` and
  `plutus-core +with-inline-r +with-cert`, which need Agda, R and Coq and make the
  solver fail outright. `cabal.project.ual` is an untracked, local-only project
  file listing just `plutus-core`, `plutus-ledger-api`, `plutus-tx` and
  `plutus-tx-plugin` with those flags off. So:
    - build: `cabal build --project-file=cabal.project.ual plutus-tx:plutus-tx-test`
    - test: `cabal test --project-file=cabal.project.ual plutus-tx:plutus-tx-test`
    - one group: `cabal run --project-file=cabal.project.ual plutus-tx:plutus-tx-test -- -p '/UAL/'`
      (tasty's `-p` filters by test-name pattern)
  Never `git add cabal.project.ual` or `.ual-build.log` — both are local scaffolding.
  Run every command from the repo root, `/Users/romainsoulat/plutus`.
- **`plutus-tx` uses `NoImplicitPrelude`** by default (see the `common lang` stanza in `plutus-tx/plutus-tx.cabal`). Every new module in `src/` must `import Prelude` explicitly. Existing blueprint modules all do this — copy that style.
- **`-Wall -Wunused-packages` and warnings are errors in CI.** Do not add a `build-depends` entry you do not use, and do not leave an unused import.
- **Golden tests**: `goldenVsText name goldenFilePath actualText` from `Test.Tasty.Extras`. On first run with no golden file, `tasty-golden` writes it — inspect it before committing. To regenerate deliberately, delete the file and re-run.
- **Changelog**: this repo uses `scriv`. A user-visible or breaking change needs a fragment file under `plutus-tx/changelog.d/`. Look at an existing fragment for the format before writing one.
- **`.git/hooks/pre-commit` is a dangling exec in this checkout**, so `git commit` fails with `cannot exec`. Use `git commit --no-verify`. This is a broken local hook, not a policy.
- **The UAL block delimiter is `{-@ … @-}`.** The UAL design doc says `-@}`; that does not compile, because `-@}` contains no `-}`. Do not "fix" the code back to the doc's spelling.

## File structure

**New library modules** (`plutus-tx/src/`), in dependency order:

| File | Responsibility |
|---|---|
| `PlutusTx/Ual/Error.hs` | `UalError` sum type + `renderUalError`. Every phase reports through this. |
| `PlutusTx/Ual/Syntax.hs` | `RawBlock`, `BlockKind`, `UalArgument`, `OnchainDecl`, `PropertyDecl`, `ModuleUal`, `LexedModule`, `UalModuleName`. Types only. |
| `PlutusTx/Ual/Lexer.hs` | `lexModule :: Text -> Either UalError LexedModule`. Finds `{-@ … @-}` blocks and `import` declarations. No interpretation of bodies. |
| `PlutusTx/Ual/Parser.hs` | `parseBlock`, `moduleUalFromSource`. Parses `ONCHAIN` and `PROPERTY` headers; `PREDICATE` and `UPLC_DATA` bodies pass through. |
| `PlutusTx/Ual/TH.hs` | `ualModule :: Q Exp`, `ualIdFor :: Name -> Q Exp`. Reads the enclosing module's source, `addDependentFile`, resolves and type-checks `ONCHAIN`/`UPLC_DATA` names. |
| `PlutusTx/Ual/Resolve.hs` | `attachUal :: [ModuleUal] -> ContractBlueprint -> Either [UalError] ContractBlueprint`. |
| `PlutusTx/Ual.hs` | Re-export module (mirrors `PlutusTx/Blueprint.hs`). |
| `PlutusTx/Assurance/Document.hs` | Document types + `ToJSON`. |
| `PlutusTx/Assurance/Build.hs` | `buildAssurance`: fragments, imports intersection, `uses` defaults, DAG and uniqueness checks. |
| `PlutusTx/Assurance/Write.hs` | `writeAssurance`, `encodeAssurance`, `blueprintRef`. |
| `PlutusTx/Assurance.hs` | Re-export module. |

**Modified library modules:**

| File | Change |
|---|---|
| `PlutusTx/Blueprint/Validator.hs` | Add `ArgumentEncoding`, `ExecutionBudget`, `AppliedArgument`; add `validatorId`, `validatorArguments`, `validatorBudget` to `ValidatorBlueprint`; add `mkValidatorBlueprint`. |
| `PlutusTx/Blueprint/PlutusVersion.hs` | Add `Eq` to `PlutusVersion` (needed by the version-agreement check). |
| `PlutusTx/Blueprint/Write.hs` | Extend the key-order list with the new keys. |
| `plutus-tx/plutus-tx.cabal` | New `exposed-modules`, new `other-modules` in the test suite, `template-haskell` is already a dep. |
| `doc/docusaurus/static/code/Example/Cip57/Blueprint/Main.hs` | Update for the new `ValidatorBlueprint` fields. |

**New test modules** (`plutus-tx/test/`):

| File | Responsibility |
|---|---|
| `Ual/Lexer/Spec.hs` | Block scanning, body byte-identity, imports, module name, error cases. |
| `Ual/Parser/Spec.hs` | `ONCHAIN` signature and option lists; `PROPERTY` header; `PREDICATE`/`UPLC_DATA`; `moduleUalFromSource`. |
| `Ual/Resolve/Spec.hs` | `attachUal` happy path and one negative per rule. |
| `Ual/Assurance/Spec.hs` | `buildAssurance` fragments/imports/uses/DAG/uniqueness + golden JSON. |
| `Ual/Blueprint/Spec.hs` | Golden JSON for a validator carrying `arguments` and `budget`. |
| `Ual/Fixture.hs` | A real annotated module carrying `$(ualModule)` — the TH integration test. |
| `Ual/Spec.hs` | Assembles the above into one `TestTree` named `UAL`. |
| `Ual/Golden/*.golden.json` | Golden files. |

Note the two `Blueprint`-named test modules: the existing `Blueprint.Spec` is a type-level module that is *not* wired into `Spec.hs`. Ours is `Ual.Blueprint.Spec` and *is* wired in, via `Ual.Spec`.

**One spec item is dropped, and the spec is wrong about it.** Spec §7 lists
"`compile`-splice generation for `ONCHAIN` functions" under `Ual.TH`, so that a
non-validator `ONCHAIN` function gets a `CompiledCode` without the author writing
one. That cannot live in `plutus-tx`: generating `$$(compile [|| f ||])` needs the
`plinthc` marker from `plutus-tx-plugin`, and `plutus-tx` cannot depend on the
plugin that depends on it. Task 12 records the spec correction. For now the author
writes the `compile` call and sets `validatorCompiled` by hand, exactly as they
already do for validators — the helper was a convenience, never a requirement.

---

### Task 1: The block lexer

**Files:**
- Create: `plutus-tx/src/PlutusTx/Ual/Error.hs`
- Create: `plutus-tx/src/PlutusTx/Ual/Syntax.hs`
- Create: `plutus-tx/src/PlutusTx/Ual/Lexer.hs`
- Create: `plutus-tx/test/Ual/Lexer/Spec.hs`
- Create: `plutus-tx/test/Ual/Spec.hs`
- Modify: `plutus-tx/plutus-tx.cabal`
- Modify: `plutus-tx/test/Spec.hs`

- [ ] **Step 1: Add the error type**

Create `plutus-tx/src/PlutusTx/Ual/Error.hs`:

```haskell
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
  = -- | Line of the opening @{-@@ that was never closed.
    UnterminatedBlock Int
  | -- | Line, and the unrecognised keyword that followed @{-@@.
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
  deriving stock (Eq, Show)

renderUalError :: UalError -> Text
renderUalError = \case
  UnterminatedBlock l ->
    atLine l "unterminated '{-@' block: no '@-}' found"
  UnknownBlockKind l kw ->
    atLine l $
      "unknown UAL block kind " <> squote kw
        <> "; expected one of ONCHAIN, PREDICATE, PROPERTY, UPLC_DATA"
  MalformedBlock l what ->
    atLine l $ "malformed UAL block: " <> what
  UnresolvedOnchainName n why ->
    "ONCHAIN " <> squote n <> ": " <> why
  ArityMismatch n declared actual ->
    "ONCHAIN " <> squote n <> ": signature declares " <> tshow declared
      <> " argument(s) but the Haskell type has " <> tshow actual
  VersionMismatch n declared preamble ->
    "ONCHAIN " <> squote n <> ": declares version " <> declared
      <> " but the blueprint preamble says " <> preamble
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
  where
    atLine l msg = "line " <> tshow l <> ": " <> msg
    squote t = "'" <> t <> "'"
    tshow :: Show a => a -> Text
    tshow = Text.pack . show
```

- [ ] **Step 2: Add the syntax types**

Two notes before you write this, both load-bearing.

**Where `ArgumentEncoding` and `ExecutionBudget` live.** They are serialised into
the blueprint, so their home is `PlutusTx.Blueprint.Validator` (Task 4 Step 3
adds them there). `Ual.Syntax` imports and re-exports them. To keep the build
green while working in order, **do Task 4 Step 3's type definitions now**, before
this step — they have no dependency on anything in Task 1.

**Which types derive `Lift`, and which must not.** The TH splice in Task 8 lifts
most of `ModuleUal` into an expression, so those types need `Lift`.
`ResolvedArgument` holds a `DefinitionId`, whose constructor
`PlutusTx.Blueprint.Definition.Id` does **not** export — a stock-derived `Lift`
would splice `MkDefinitionId` into a module where that name is out of scope, and
fail at the use site. So `ResolvedArgument`, `OnchainDecl` and `ModuleUal` get no
`Lift` instance; Task 8 builds those three as expressions field by field. Do not
"tidy" this by adding `deriving Lift` to them.

Create `plutus-tx/src/PlutusTx/Ual/Syntax.hs`:

```haskell
{-# LANGUAGE DerivingStrategies #-}

module PlutusTx.Ual.Syntax
  ( UalModuleName (..)
  , BlockKind (..)
  , RawBlock (..)
  , LexedModule (..)
  , ArgumentEncoding (..)
  , ExecutionBudget (..)
  , UalArgument (..)
  , ResolvedArgument (..)
  , OnchainDecl (..)
  , PropertyDecl (..)
  , UalBlock (..)
  , ModuleUal (..)
  , emptyModuleUal
  ) where

import Prelude

import Data.Text (Text)
import Language.Haskell.TH.Syntax (Lift)
import PlutusTx.Blueprint.Definition.Id (DefinitionId)
import PlutusTx.Blueprint.PlutusVersion (PlutusVersion)
import PlutusTx.Blueprint.Validator (ArgumentEncoding (..), ExecutionBudget (..))

-- | A surface-language module name, e.g. @"MyContract.Types"@.
newtype UalModuleName = UalModuleName Text
  deriving stock (Eq, Ord, Show, Lift)

data BlockKind = KOnchain | KPredicate | KProperty | KUplcData
  deriving stock (Eq, Ord, Show)

{-| A @{-@@ … @@-}@ block exactly as the lexer found it: the kind keyword, and
everything after it, untouched. -}
data RawBlock = RawBlock
  { rawKind :: BlockKind
  , rawBody :: Text
  -- ^ Everything after the kind keyword, verbatim, with no trimming.
  , rawLine :: Int
  -- ^ 1-based line of the opening @{-@@.
  }
  deriving stock (Eq, Show)

data LexedModule = LexedModule
  { lexedModuleName :: Maybe UalModuleName
  , lexedImports :: [UalModuleName]
  , lexedBlocks :: [RawBlock]
  }
  deriving stock (Eq, Show)

{-| One argument of an @ONCHAIN@ refined signature, as written. Positional: UAL
gives types, not names. -}
data UalArgument = UalArgument
  { argTypeName :: Text
  -- ^ Source text of the type, e.g. @"CurrencySymbol"@.
  , argEncoding :: ArgumentEncoding
  }
  deriving stock (Eq, Show, Lift)

{-| A 'UalArgument' whose type name has been resolved to a blueprint definition
id. Produced only by the TH splice, which is the only place that has the type
itself. No 'Lift' instance — see the note in Task 1 Step 2. -}
data ResolvedArgument = ResolvedArgument
  { resolvedEncoding :: ArgumentEncoding
  , resolvedDefinitionId :: DefinitionId
  }
  deriving stock (Eq, Show)

data OnchainDecl = OnchainDecl
  { onchainName :: Text
  , onchainArgs :: [UalArgument]
  , onchainResult :: Text
  -- ^ Source text of the result type. Unused in this slice; the generator needs it.
  , onchainVersion :: Maybe PlutusVersion
  , onchainBudget :: Maybe ExecutionBudget
  , onchainLine :: Int
  , onchainResolvedArgs :: [ResolvedArgument]
  {-^ Empty as the parser produces it; filled by
  'PlutusTx.Ual.TH.ualModule'. -}
  }
  deriving stock (Eq, Show)

data PropertyDecl = PropertyDecl
  { propertyName :: Text
  , propertyText :: Text
  -- ^ The natural-language statement.
  , propertyBody :: Text
  -- ^ The formal statement, verbatim.
  , propertyLine :: Int
  }
  deriving stock (Eq, Show, Lift)

-- | A parsed UAL block.
data UalBlock
  = BOnchain OnchainDecl
  | BPredicate Text
  -- ^ The body, verbatim.
  | BProperty PropertyDecl
  | BUplcData Text
  -- ^ The type name.
  deriving stock (Eq, Show)

-- | Everything one surface module contributes.
data ModuleUal = ModuleUal
  { ualModuleName :: UalModuleName
  , ualModuleImports :: [UalModuleName]
  , ualOnchain :: [OnchainDecl]
  , ualPredicates :: [Text]
  -- ^ @PREDICATE@ bodies, in source order.
  , ualProperties :: [PropertyDecl]
  , ualUplcData :: [Text]
  }
  deriving stock (Eq, Show)

emptyModuleUal :: UalModuleName -> ModuleUal
emptyModuleUal n = ModuleUal n [] [] [] [] []
```

`UalBlock` is declared here rather than in `Ual.Parser` so that Task 2 and Task 3
add no types, only functions.

- [ ] **Step 3: Write the failing lexer tests**

Create `plutus-tx/test/Ual/Lexer/Spec.hs`:

```haskell
{-# LANGUAGE OverloadedStrings #-}

module Ual.Lexer.Spec (tests) where

import Prelude

import Data.Text (Text)
import Data.Text qualified as Text
import PlutusTx.Ual.Error (UalError (..))
import PlutusTx.Ual.Lexer (lexModule)
import PlutusTx.Ual.Syntax
  ( BlockKind (..)
  , LexedModule (..)
  , RawBlock (..)
  , UalModuleName (..)
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

tests :: TestTree
tests =
  testGroup
    "Lexer"
    [ testCase "module name" $
        lexedModuleName <$> lexModule "module Foo.Bar where\n"
          @?= Right (Just (UalModuleName "Foo.Bar"))
    , testCase "no module header" $
        lexedModuleName <$> lexModule "x = 1\n" @?= Right Nothing
    , testCase "imports, plain and qualified and aliased" $
        lexedImports
          <$> lexModule
            ( Text.unlines
                [ "module M where"
                , "import Foo.Bar"
                , "import qualified Baz.Qux as Q"
                , "import Data.Text (Text)"
                , "x = 1"
                , "import NotAnImport.Because.Indented"
                ]
            )
          @?= Right
            [ UalModuleName "Foo.Bar"
            , UalModuleName "Baz.Qux"
            , UalModuleName "Data.Text"
            , UalModuleName "NotAnImport.Because.Indented"
            ]
    , testCase "one block of each kind, in source order" $
        (fmap rawKind . lexedBlocks)
          <$> lexModule
            ( Text.unlines
                [ "{-@ ONCHAIN a @-}"
                , "{-@ PREDICATE b @-}"
                , "{-@ PROPERTY c @-}"
                , "{-@ UPLC_DATA d @-}"
                ]
            )
          @?= Right [KOnchain, KPredicate, KProperty, KUplcData]
    , testCase "body is byte-identical, including Unicode and nested braces" $
        (fmap rawBody . lexedBlocks) <$> lexModule ("{-@ PREDICATE " <> tricky <> " @-}")
          @?= Right [" " <> tricky <> " "]
    , testCase "line numbers are 1-based and count preceding newlines" $
        (fmap rawLine . lexedBlocks)
          <$> lexModule "module M where\n\n{-@ ONCHAIN a @-}\nx = 1\n{-@ PROPERTY b @-}\n"
          @?= Right [3, 5]
    , testCase "unterminated block reports the opening line" $
        lexModule "module M where\n{-@ ONCHAIN a -@}\n" @?= Left (UnterminatedBlock 2)
    , testCase "unknown kind reports the keyword" $
        lexModule "{-@ NOPE a @-}\n" @?= Left (UnknownBlockKind 1 "NOPE")
    , testCase "an ordinary comment is not a block" $
        (length . lexedBlocks) <$> lexModule "{- ONCHAIN not a block -}\n" @?= Right 0
    ]

-- | Unicode, a Lean comment, and an unbalanced Haskell comment opener.
tricky :: Text
tricky = "∀ x, x → x {- not a comment terminator -} /- lean -/"
```

Wire it up. Create `plutus-tx/test/Ual/Spec.hs`:

```haskell
module Ual.Spec (tests) where

import Prelude

import Test.Tasty (TestTree, testGroup)
import Ual.Lexer.Spec qualified

tests :: TestTree
tests = testGroup "UAL" [Ual.Lexer.Spec.tests]
```

In `plutus-tx/test/Spec.hs`, add the import next to the other qualified test imports:

```haskell
import Ual.Spec qualified
```

and add `Ual.Spec.tests` as the last entry of the `tests` list (after `Blueprint.Definition.Spec.tests`).

In `plutus-tx/plutus-tx.cabal`, add to the `library` stanza's `exposed-modules`, keeping alphabetical order (they sort after `PlutusTx.TH`):

```
    PlutusTx.Ual.Error
    PlutusTx.Ual.Lexer
    PlutusTx.Ual.Syntax
```

and to the `test-suite plutus-tx-test` stanza's `other-modules`, in alphabetical order:

```
    Ual.Lexer.Spec
    Ual.Spec
```

- [ ] **Step 4: Run the tests to verify they fail**

Run: `cabal test plutus-tx:plutus-tx-test`
Expected: build failure, `Could not find module 'PlutusTx.Ual.Lexer'`.

- [ ] **Step 5: Implement the lexer**

Create `plutus-tx/src/PlutusTx/Ual/Lexer.hs`:

```haskell
{-# LANGUAGE OverloadedStrings #-}

module PlutusTx.Ual.Lexer
  ( lexModule
  , blockOpen
  , blockClose
  ) where

import Prelude

import Data.Text (Text)
import Data.Text qualified as Text
import PlutusTx.Ual.Error (UalError (..))
import PlutusTx.Ual.Syntax
  ( BlockKind (..)
  , LexedModule (..)
  , RawBlock (..)
  , UalModuleName (..)
  )

blockOpen :: Text
blockOpen = "{-@"

{-| Note the spelling. The UAL design doc writes @-@}@, which is not a Haskell
comment terminator (it contains no @-}@) and makes the enclosing file fail to
lex with "unterminated '{-'". -}
blockClose :: Text
blockClose = "@-}"

{-| Scan a surface-language source file for UAL blocks, its module name, and its
import list, in one pass. Bodies are not interpreted: see
'PlutusTx.Ual.Parser'. -}
lexModule :: Text -> Either UalError LexedModule
lexModule src = do
  blocks <- scan 1 src
  pure
    LexedModule
      { lexedModuleName = firstJust (moduleNameOf <$> lines')
      , lexedImports = concatMap (maybe [] pure . importOf) lines'
      , lexedBlocks = blocks
      }
  where
    lines' = Text.lines src

    firstJust :: [Maybe a] -> Maybe a
    firstJust xs = case [a | Just a <- xs] of
      a : _ -> Just a
      [] -> Nothing

    -- Walk the source looking for `{-@`, tracking the current line number.
    scan :: Int -> Text -> Either UalError [RawBlock]
    scan line rest =
      let (before, atOpen) = Text.breakOn blockOpen rest
          line' = line + Text.count "\n" before
       in if Text.null atOpen
            then Right []
            else
              let afterOpen = Text.drop (Text.length blockOpen) atOpen
                  (body, atClose) = Text.breakOn blockClose afterOpen
               in if Text.null atClose
                    then Left (UnterminatedBlock line')
                    else do
                      kind <- kindOf line' body
                      let bodyAfterKeyword = dropKeyword body
                          after = Text.drop (Text.length blockClose) atClose
                          nextLine = line' + Text.count "\n" body
                      rest' <- scan nextLine after
                      pure (RawBlock kind bodyAfterKeyword line' : rest')

    -- The keyword is the first whitespace-delimited word of the block.
    keywordOf :: Text -> Text
    keywordOf = Text.takeWhile (not . isSpaceChar) . Text.dropWhile isSpaceChar

    -- Everything after the keyword, verbatim. Leading whitespace before the
    -- keyword is dropped; nothing else is touched.
    dropKeyword :: Text -> Text
    dropKeyword body =
      let stripped = Text.dropWhile isSpaceChar body
       in Text.drop (Text.length (keywordOf body)) stripped

    kindOf :: Int -> Text -> Either UalError BlockKind
    kindOf line body = case keywordOf body of
      "ONCHAIN" -> Right KOnchain
      "PREDICATE" -> Right KPredicate
      "PROPERTY" -> Right KProperty
      "UPLC_DATA" -> Right KUplcData
      other -> Left (UnknownBlockKind line other)

    isSpaceChar :: Char -> Bool
    isSpaceChar c = c == ' ' || c == '\t' || c == '\n' || c == '\r'

-- | @module Foo.Bar where@ -> @Foo.Bar@. Only matches at column 0.
moduleNameOf :: Text -> Maybe UalModuleName
moduleNameOf l = case Text.words l of
  "module" : name : _ -> Just (UalModuleName (Text.dropWhileEnd (== '(') name))
  _ -> Nothing

{-| @import [qualified] Foo.Bar [as Q] [(…)]@ -> @Foo.Bar@. Only matches at
column 0, which is where Haskell import declarations live. -}
importOf :: Text -> Maybe UalModuleName
importOf l = case Text.words l of
  "import" : "qualified" : name : _ -> Just (UalModuleName (clean name))
  "import" : name : _ -> Just (UalModuleName (clean name))
  _ -> Nothing
  where
    clean = Text.takeWhile (\c -> c /= '(' && c /= ',')
```

Note on `importOf`: the test asserts that an *indented* `import` line is still
collected. `Text.words` ignores leading whitespace, so it is. That is deliberate
— over-collecting an import is harmless (Task 7 intersects against the set of
modules that actually produced fragments), whereas missing one loses a real
dependency edge.

- [ ] **Step 6: Run the tests to verify they pass**

Run: `cabal test plutus-tx:plutus-tx-test`
Expected: PASS, including all nine `UAL.Lexer` cases.

- [ ] **Step 7: Add a property test for body byte-identity**

Append to `plutus-tx/test/Ual/Lexer/Spec.hs`. Add these imports at the top:

```haskell
import Hedgehog (Property, forAll, property, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty.Hedgehog (testPropertyNamed)
```

Add to the `tests` list:

```haskell
    , testPropertyNamed "bodies survive lexing unchanged" "bodyRoundTrip" bodyRoundTrip
```

and at the bottom of the module:

```haskell
{-| Any text that does not contain the terminator must come back byte-identical.
This is the guarantee the whole pass-through design rests on. -}
bodyRoundTrip :: Property
bodyRoundTrip = property $ do
  body <- forAll $ Gen.filter (not . Text.isInfixOf "@-}") (Gen.text (Range.linear 0 200) Gen.unicode)
  let src = "{-@ PREDICATE" <> body <> "@-}"
  (fmap rawBody . lexedBlocks) <$> lexModule src === Right [body]
```

- [ ] **Step 8: Run it**

Run: `cabal run plutus-tx:plutus-tx-test -- -p '/bodies survive/'`
Expected: PASS, `1 test passed`.

- [ ] **Step 9: Commit**

```bash
git add plutus-tx/src/PlutusTx/Ual plutus-tx/test/Ual plutus-tx/test/Spec.hs plutus-tx/plutus-tx.cabal
git commit --no-verify -m "feat(plutus-tx): UAL block lexer"
```

---

### Task 2: The ONCHAIN header parser

**Files:**
- Create: `plutus-tx/src/PlutusTx/Ual/Parser.hs`
- Create: `plutus-tx/test/Ual/Parser/Spec.hs`
- Modify: `plutus-tx/plutus-tx.cabal`
- Modify: `plutus-tx/test/Ual/Spec.hs`

- [ ] **Step 1: Write the failing tests**

Create `plutus-tx/test/Ual/Parser/Spec.hs`:

```haskell
{-# LANGUAGE OverloadedStrings #-}

module Ual.Parser.Spec (tests) where

import Prelude

import Data.Text qualified as Text
import PlutusTx.Blueprint.PlutusVersion (PlutusVersion (..))
import PlutusTx.Ual.Error (UalError (..))
import PlutusTx.Ual.Parser (parseBlock)
import PlutusTx.Ual.Syntax
  ( ArgumentEncoding (..)
  , BlockKind (..)
  , ExecutionBudget (..)
  , OnchainDecl (..)
  , RawBlock (..)
  , UalArgument (..)
  , UalBlock (..)
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

tests :: TestTree
tests = testGroup "Parser" [onchainTests]

onchain :: Text.Text -> Either UalError UalBlock
onchain body = parseBlock (RawBlock KOnchain body 7)

onchainTests :: TestTree
onchainTests =
  testGroup
    "ONCHAIN"
    [ testCase "bare signature, no options, asData by default" $
        onchain " f :: Integer -> Bool "
          @?= Right
            ( BOnchain
                OnchainDecl
                  { onchainName = "f"
                  , onchainArgs = [UalArgument "Integer" AsData]
                  , onchainResult = "Bool"
                  , onchainVersion = Nothing
                  , onchainBudget = Nothing
                  , onchainLine = 7
                  , onchainResolvedArgs = []
                  }
            )
    , testCase "braced encodings, both schemes" $
        (fmap onchainArgs . asOnchain)
          <$> onchain " f :: { A : asData } -> { B : asScott } -> () "
          @?= Right (Just [UalArgument "A" AsData, UalArgument "B" AsScott])
    , testCase "mixed braced and bare arguments" $
        (fmap onchainArgs . asOnchain) <$> onchain " f :: A -> { B : asScott } -> () "
          @?= Right (Just [UalArgument "A" AsData, UalArgument "B" AsScott])
    , testCase "single colon form is also accepted" $
        (fmap onchainName . asOnchain) <$> onchain " f : A -> () "
          @?= Right (Just "f")
    , testCase "version option" $
        (fmap onchainVersion . asOnchain) <$> onchain " [version: PlutusV3] f :: A -> () "
          @?= Right (Just (Just PlutusV3))
    , testCase "budget option, both fields" $
        (fmap onchainBudget . asOnchain)
          <$> onchain " [exCPU: 1883313, exMem: 12342] f :: A -> () "
          @?= Right (Just (Just (MkExecutionBudget 1883313 12342)))
    , testCase "both options, either order" $
        (fmap onchainVersion . asOnchain)
          <$> onchain " [exCPU: 1, exMem: 2] [version: PlutusV2] f :: A -> () "
          @?= Right (Just (Just PlutusV2))
    , testCase "multi-line signature" $
        (fmap onchainArgs . asOnchain)
          <$> onchain
            ( Text.unlines
                [ " [version: PlutusV3]"
                , "    mintingContract :: { CurrencySymbol : asData }"
                , "                    -> { ScriptContext  : asData }"
                , "                    -> ()"
                ]
            )
          @?= Right
            ( Just
                [ UalArgument "CurrencySymbol" AsData
                , UalArgument "ScriptContext" AsData
                ]
            )
    , testCase "nullary function is an error, there is nothing to apply" $
        onchain " f :: () " @?= Left (MalformedBlock 7 "signature has no arguments")
    , testCase "missing signature separator" $
        onchain " f A -> () " @?= Left (MalformedBlock 7 "expected '::' or ':' after the name")
    , testCase "unknown encoding scheme" $
        onchain " f :: { A : asBytes } -> () "
          @?= Left (MalformedBlock 7 "unknown encoding 'asBytes'; expected asData or asScott")
    , testCase "unknown plutus version" $
        onchain " [version: PlutusV9] f :: A -> () "
          @?= Left (MalformedBlock 7 "unknown version 'PlutusV9'")
    , testCase "budget missing exMem" $
        onchain " [exCPU: 1] f :: A -> () "
          @?= Left (MalformedBlock 7 "budget needs both exCPU and exMem")
    ]

asOnchain :: UalBlock -> Maybe OnchainDecl
asOnchain = \case
  BOnchain d -> Just d
  _ -> Nothing
```

Note this test module needs `{-# LANGUAGE LambdaCase #-}` for `asOnchain`. Add it.

Add to `plutus-tx/test/Ual/Spec.hs`:

```haskell
import Ual.Parser.Spec qualified
```

and `Ual.Parser.Spec.tests` to the list. Add `Ual.Parser.Spec` to the test suite's
`other-modules` and `PlutusTx.Ual.Parser` to the library's `exposed-modules`.

- [ ] **Step 2: Run to verify failure**

Run: `cabal test plutus-tx:plutus-tx-test`
Expected: build failure, `Could not find module 'PlutusTx.Ual.Parser'`.

- [ ] **Step 3: Implement the ONCHAIN parser**

Create `plutus-tx/src/PlutusTx/Ual/Parser.hs`. This step covers `ONCHAIN` only, so
the other three `parseBlock` branches return a `MalformedBlock` saying so — that
keeps the module total and the build warning-free while only `ONCHAIN` has tests.
Task 3 Step 3 replaces all three branches with their real implementations, and
gives the full replacement code. This is a deliberate intermediate state, not an
unfinished step: nothing in Task 2's tests exercises those branches.

```haskell
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusTx.Ual.Parser
  ( parseBlock
  ) where

import Prelude

import Data.Char qualified as Char
import Data.Text (Text)
import Data.Text qualified as Text
import PlutusTx.Blueprint.PlutusVersion (PlutusVersion (..))
import PlutusTx.Ual.Error (UalError (..))
import PlutusTx.Ual.Syntax
  ( ArgumentEncoding (..)
  , BlockKind (..)
  , ExecutionBudget (..)
  , OnchainDecl (..)
  , PropertyDecl (..)
  , RawBlock (..)
  , UalArgument (..)
  , UalBlock (..)
  )

parseBlock :: RawBlock -> Either UalError UalBlock
parseBlock rb = case rawKind rb of
  KOnchain -> BOnchain <$> parseOnchain (rawLine rb) (rawBody rb)
  KPredicate -> Left (MalformedBlock (rawLine rb) "PREDICATE not implemented yet")
  KProperty -> Left (MalformedBlock (rawLine rb) "PROPERTY not implemented yet")
  KUplcData -> Left (MalformedBlock (rawLine rb) "UPLC_DATA not implemented yet")

----------------------------------------------------------------------------------------------------
-- ONCHAIN -----------------------------------------------------------------------------------------

{-| @[version: V] [exCPU: n, exMem: m] name :: { T : enc } -> … -> Result@

Option groups come first, in any order, and are both optional. The signature
separator may be @::@ (Haskell) or @:@ (Aiken, Scalus). -}
parseOnchain :: Int -> Text -> Either UalError OnchainDecl
parseOnchain line body = do
  (opts, afterOpts) <- takeOptions line (Text.strip body)
  version <- traverse (parseVersion line) (lookup "version" opts)
  budget <- parseBudget line opts
  (name, sig) <- splitSignature line afterOpts
  parts <- pure (splitArrows sig)
  case reverse parts of
    [] -> Left (MalformedBlock line "signature has no arguments")
    [_] -> Left (MalformedBlock line "signature has no arguments")
    result : revArgs -> do
      args <- traverse (parseArgument line) (reverse revArgs)
      pure
        OnchainDecl
          { onchainName = name
          , onchainArgs = args
          , onchainResult = Text.strip result
          , onchainVersion = version
          , onchainBudget = budget
          , onchainLine = line
          , onchainResolvedArgs = []
          }

-- | Peel leading @[k: v, k: v]@ groups, returning their key/value pairs.
takeOptions :: Int -> Text -> Either UalError ([(Text, Text)], Text)
takeOptions line t
  | Just afterBracket <- Text.stripPrefix "[" (Text.stripStart t) =
      case Text.breakOn "]" afterBracket of
        (_, rest) | Text.null rest -> Left (MalformedBlock line "unclosed '[' in options")
        (inside, rest) -> do
          pairs <- traverse (parsePair line) (Text.splitOn "," inside)
          (more, final) <- takeOptions line (Text.drop 1 rest)
          pure (pairs <> more, final)
  | otherwise = Right ([], t)

parsePair :: Int -> Text -> Either UalError (Text, Text)
parsePair line kv = case Text.breakOn ":" kv of
  (_, rest) | Text.null rest -> Left (MalformedBlock line ("option '" <> Text.strip kv <> "' needs a value"))
  (k, v) -> Right (Text.strip k, Text.strip (Text.drop 1 v))

parseVersion :: Int -> Text -> Either UalError PlutusVersion
parseVersion line = \case
  "PlutusV1" -> Right PlutusV1
  "PlutusV2" -> Right PlutusV2
  "PlutusV3" -> Right PlutusV3
  "PlutusV4" -> Right PlutusV4
  other -> Left (MalformedBlock line ("unknown version '" <> other <> "'"))

parseBudget :: Int -> [(Text, Text)] -> Either UalError (Maybe ExecutionBudget)
parseBudget line opts = case (lookup "exCPU" opts, lookup "exMem" opts) of
  (Nothing, Nothing) -> Right Nothing
  (Just c, Just m) -> Just <$> (MkExecutionBudget <$> nat c <*> nat m)
  _ -> Left (MalformedBlock line "budget needs both exCPU and exMem")
  where
    nat v
      | Text.all Char.isDigit v && not (Text.null v) = Right (read (Text.unpack v))
      | otherwise = Left (MalformedBlock line ("'" <> v <> "' is not a non-negative integer"))

-- | @name :: rest@ or @name : rest@.
splitSignature :: Int -> Text -> Either UalError (Text, Text)
splitSignature line t = case Text.breakOn "::" t of
  (n, rest) | not (Text.null rest) -> Right (Text.strip n, Text.drop 2 rest)
  _ -> case Text.breakOn ":" t of
    (n, rest) | not (Text.null rest) -> Right (Text.strip n, Text.drop 1 rest)
    _ -> Left (MalformedBlock line "expected '::' or ':' after the name")

{-| Split on top-level @->@. Brace groups cannot contain arrows, so a plain
split is sufficient. -}
splitArrows :: Text -> [Text]
splitArrows = Text.splitOn "->"

-- | @{ T : enc }@ or a bare @T@ (which means @asData@).
parseArgument :: Int -> Text -> Either UalError UalArgument
parseArgument line raw =
  let t = Text.strip raw
   in case Text.stripPrefix "{" t >>= \i -> Text.stripSuffix "}" (Text.strip i) of
        Nothing
          | Text.null t -> Left (MalformedBlock line "empty argument type")
          | otherwise -> Right (UalArgument t AsData)
        Just inner -> case Text.breakOn ":" inner of
          (ty, rest)
            | Text.null rest -> Right (UalArgument (Text.strip ty) AsData)
            | otherwise -> do
                enc <- parseEncoding line (Text.strip (Text.drop 1 rest))
                pure (UalArgument (Text.strip ty) enc)

parseEncoding :: Int -> Text -> Either UalError ArgumentEncoding
parseEncoding line = \case
  "asData" -> Right AsData
  "asScott" -> Right AsScott
  other ->
    Left
      ( MalformedBlock
          line
          ("unknown encoding '" <> other <> "'; expected asData or asScott")
      )
```

`PropertyDecl` is imported but unused until Task 3. To keep `-Wall` clean now,
omit it from the import list in this step and add it in Task 3.

- [ ] **Step 4: Run to verify pass**

Run: `cabal run plutus-tx:plutus-tx-test -- -p '/ONCHAIN/'`
Expected: PASS, 13 tests.

- [ ] **Step 5: Commit**

```bash
git add plutus-tx/src/PlutusTx/Ual plutus-tx/test/Ual plutus-tx/plutus-tx.cabal
git commit --no-verify -m "feat(plutus-tx): parse UAL ONCHAIN refined signatures"
```

---

### Task 3: PREDICATE, PROPERTY, UPLC_DATA, and `ModuleUal` assembly

**Files:**
- Modify: `plutus-tx/src/PlutusTx/Ual/Parser.hs`
- Modify: `plutus-tx/test/Ual/Parser/Spec.hs`

- [ ] **Step 1: Write the failing tests**

Add to `plutus-tx/test/Ual/Parser/Spec.hs`. Extend the imports with:

```haskell
import PlutusTx.Ual.Parser (moduleUalFromSource, parseBlock)
import PlutusTx.Ual.Syntax (ModuleUal (..), PropertyDecl (..), UalModuleName (..))
```

Add `otherKindTests` and `assemblyTests` to the top-level `tests` list, then:

```haskell
otherKindTests :: TestTree
otherKindTests =
  testGroup
    "other kinds"
    [ testCase "PREDICATE body passes through verbatim" $
        parseBlock (RawBlock KPredicate "\ndef p (x : Int) : Prop := x > 0\n" 3)
          @?= Right (BPredicate "\ndef p (x : Int) : Prop := x > 0\n")
    , testCase "UPLC_DATA takes a single type name" $
        parseBlock (RawBlock KUplcData "  SellDatum  " 4) @?= Right (BUplcData "SellDatum")
    , testCase "UPLC_DATA rejects two names" $
        parseBlock (RawBlock KUplcData " A B " 4)
          @?= Left (MalformedBlock 4 "expected exactly one type name")
    , testCase "PROPERTY: name, quoted text, body after the colon" $
        parseBlock
          ( RawBlock
              KProperty
              " p_one\n  \"Funds cannot be locked.\"\n : \8704 x, x \8594 x\n"
              9
          )
          @?= Right
            ( BProperty
                PropertyDecl
                  { propertyName = "p_one"
                  , propertyText = "Funds cannot be locked."
                  , propertyBody = "\8704 x, x \8594 x"
                  , propertyLine = 9
                  }
            )
    , testCase "PROPERTY body keeps internal newlines and indentation" $
        (fmap propertyBody . asProperty)
          <$> parseBlock (RawBlock KProperty " p \"t\" : a \8594\n    b\n" 1)
          @?= Right (Just "a \8594\n    b")
    , testCase "PROPERTY without text is rejected" $
        parseBlock (RawBlock KProperty " p : True " 1)
          @?= Left (MalformedBlock 1 "expected a quoted natural-language statement after the name")
    , testCase "PROPERTY without a body separator is rejected" $
        parseBlock (RawBlock KProperty " p \"t\" " 1)
          @?= Left (MalformedBlock 1 "expected ':' before the formal statement")
    ]

asProperty :: UalBlock -> Maybe PropertyDecl
asProperty = \case
  BProperty d -> Just d
  _ -> Nothing

assemblyTests :: TestTree
assemblyTests =
  testGroup
    "moduleUalFromSource"
    [ testCase "collects every kind, predicates in source order" $
        moduleUalFromSource (UalModuleName "Fallback") source
          @?= Right
            ModuleUal
              { ualModuleName = UalModuleName "My.Contract"
              , ualModuleImports = [UalModuleName "My.Types"]
              , ualOnchain =
                  [ OnchainDecl
                      { onchainName = "v"
                      , onchainArgs = [UalArgument "A" AsData]
                      , onchainResult = "()"
                      , onchainVersion = Nothing
                      , onchainBudget = Nothing
                      , onchainLine = 4
                      , onchainResolvedArgs = []
                      }
                  ]
              , ualPredicates = ["\ndef first : Prop := True\n", "\ndef second : Prop := True\n"]
              , ualProperties =
                  [ PropertyDecl
                      { propertyName = "p"
                      , propertyText = "t"
                      , propertyBody = "True"
                      , propertyLine = 11
                      }
                  ]
              , ualUplcData = ["D"]
              }
    , testCase "falls back to the supplied name when there is no module header" $
        (ualModuleName <$> moduleUalFromSource (UalModuleName "Fallback") "{-@ UPLC_DATA D @-}\n")
          @?= Right (UalModuleName "Fallback")
    , testCase "propagates a lexer error" $
        moduleUalFromSource (UalModuleName "M") "{-@ ONCHAIN x -@}\n"
          @?= Left (UnterminatedBlock 1)
    ]
  where
    source =
      Text.unlines
        [ "module My.Contract where" -- 1
        , "import My.Types" --           2
        , "" --                          3
        , "{-@ ONCHAIN v :: A -> () @-}" -- 4
        , "{-@ PREDICATE" --             5
        , "def first : Prop := True" --  6
        , "@-}" --                       7
        , "{-@ PREDICATE" --             8
        , "def second : Prop := True" -- 9
        , "@-}" --                      10
        , "{-@ PROPERTY p \"t\" : True @-}" -- 11
        , "{-@ UPLC_DATA D @-}" --       12
        ]
```

- [ ] **Step 2: Run to verify failure**

Run: `cabal test plutus-tx:plutus-tx-test`
Expected: build failure, `Variable not in scope: moduleUalFromSource`.

- [ ] **Step 3: Implement the remaining parsers and the assembler**

In `plutus-tx/src/PlutusTx/Ual/Parser.hs`: add `moduleUalFromSource` to the export list, add `PropertyDecl (..)` and `ModuleUal (..)`, `LexedModule (..)`, `UalModuleName` to the `Syntax` import list, add `import PlutusTx.Ual.Lexer (lexModule)`, then replace the three stub branches of `parseBlock` and append the new functions:

```haskell
parseBlock :: RawBlock -> Either UalError UalBlock
parseBlock rb = case rawKind rb of
  KOnchain -> BOnchain <$> parseOnchain (rawLine rb) (rawBody rb)
  KPredicate -> Right (BPredicate (rawBody rb))
  KProperty -> BProperty <$> parseProperty (rawLine rb) (rawBody rb)
  KUplcData -> BUplcData <$> parseUplcData (rawLine rb) (rawBody rb)

----------------------------------------------------------------------------------------------------
-- UPLC_DATA ---------------------------------------------------------------------------------------

parseUplcData :: Int -> Text -> Either UalError Text
parseUplcData line body = case Text.words body of
  [n] -> Right n
  _ -> Left (MalformedBlock line "expected exactly one type name")

----------------------------------------------------------------------------------------------------
-- PROPERTY ----------------------------------------------------------------------------------------

{-| @name "natural language" : formal statement@

The natural-language string is required: the assurance document's
@statement.text@ is REQUIRED and there is no other source for it. -}
parseProperty :: Int -> Text -> Either UalError PropertyDecl
parseProperty line body = do
  let afterName = Text.stripStart body
      (name, rest0) = Text.break (\c -> c == '"' || c == ':') afterName
  (text, rest1) <- takeQuoted line (Text.stripStart rest0)
  formal <- case Text.stripPrefix ":" (Text.stripStart rest1) of
    Nothing -> Left (MalformedBlock line "expected ':' before the formal statement")
    Just f -> Right (Text.strip f)
  pure
    PropertyDecl
      { propertyName = Text.strip name
      , propertyText = text
      , propertyBody = formal
      , propertyLine = line
      }

{-| Take a @"…"@ literal. Backslash escapes are not supported: a
natural-language statement has no need of them, and rejecting them keeps the
lexer honest about what it accepts. -}
takeQuoted :: Int -> Text -> Either UalError (Text, Text)
takeQuoted line t = case Text.stripPrefix "\"" t of
  Nothing ->
    Left (MalformedBlock line "expected a quoted natural-language statement after the name")
  Just afterOpen -> case Text.breakOn "\"" afterOpen of
    (_, rest) | Text.null rest -> Left (MalformedBlock line "unterminated string literal")
    (inside, rest) -> Right (Text.strip (unwrapLines inside), Text.drop 1 rest)
  where
    -- A statement may be wrapped across source lines; collapse the wrapping.
    unwrapLines = Text.unwords . Text.words

----------------------------------------------------------------------------------------------------
-- Assembly ----------------------------------------------------------------------------------------

{-| Lex and parse a whole surface module. @fallbackName@ is used when the source
has no @module@ header. -}
moduleUalFromSource :: UalModuleName -> Text -> Either UalError ModuleUal
moduleUalFromSource fallbackName src = do
  lexed <- lexModule src
  blocks <- traverse parseBlock (lexedBlocks lexed)
  let base =
        ModuleUal
          { ualModuleName = maybe fallbackName id (lexedModuleName lexed)
          , ualModuleImports = lexedImports lexed
          , ualOnchain = []
          , ualPredicates = []
          , ualProperties = []
          , ualUplcData = []
          }
  pure (foldl addBlock base blocks)
  where
    -- Appends keep source order; the lists are short.
    addBlock m = \case
      BOnchain d -> m {ualOnchain = ualOnchain m <> [d]}
      BPredicate b -> m {ualPredicates = ualPredicates m <> [b]}
      BProperty d -> m {ualProperties = ualProperties m <> [d]}
      BUplcData n -> m {ualUplcData = ualUplcData m <> [n]}
```

- [ ] **Step 4: Run to verify pass**

Run: `cabal run plutus-tx:plutus-tx-test -- -p '/Parser/'`
Expected: PASS, 23 tests.

- [ ] **Step 5: Commit**

```bash
git add plutus-tx/src/PlutusTx/Ual plutus-tx/test/Ual
git commit --no-verify -m "feat(plutus-tx): parse UAL predicates, properties and data blocks"
```

---

### Task 4: Blueprint validator fields

**Files:**
- Modify: `plutus-tx/src/PlutusTx/Blueprint/Validator.hs`
- Modify: `plutus-tx/src/PlutusTx/Blueprint/PlutusVersion.hs`
- Modify: `plutus-tx/src/PlutusTx/Blueprint/Write.hs`
- Modify: `plutus-tx/src/PlutusTx/Ual/Syntax.hs`
- Create: `plutus-tx/test/Ual/Blueprint/Spec.hs`
- Create: `plutus-tx/test/Ual/Golden/validator-arguments.golden.json`
- Modify: `doc/docusaurus/static/code/Example/Cip57/Blueprint/Main.hs`
- Modify: `plutus-tx-plugin/test/Blueprint/Tests.hs`
- Create: `plutus-tx/changelog.d/20260824_000000_ual_validator_fields.md`

- [ ] **Step 1: Write the failing golden test**

Create `plutus-tx/test/Ual/Blueprint/Spec.hs`:

```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Ual.Blueprint.Spec (tests) where

import Prelude

import Data.ByteString.Lazy qualified as LBS
import Data.Set qualified as Set
import Data.Text.Encoding qualified as Text
import GHC.Generics (Generic)
import PlutusTx.Blueprint.Argument (ArgumentBlueprint (..))
import PlutusTx.Blueprint.Contract (ContractBlueprint (..))
import PlutusTx.Blueprint.Definition (HasBlueprintDefinition, definitionRef, deriveDefinitions)
import PlutusTx.Blueprint.PlutusVersion (PlutusVersion (..))
import PlutusTx.Blueprint.Preamble (Preamble (..))
import PlutusTx.Blueprint.Purpose qualified as Purpose
import PlutusTx.Blueprint.Validator
  ( AppliedArgument (..)
  , ArgumentEncoding (..)
  , ExecutionBudget (..)
  , mkValidatorBlueprint
  , validatorArguments
  , validatorBudget
  , validatorId
  , validatorRedeemer
  , validatorTitle
  )
import PlutusTx.Blueprint.Write (encodeBlueprint)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Extras (goldenVsText)

newtype Ticket = MkTicket Integer
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)

tests :: TestTree
tests =
  testGroup
    "Blueprint"
    [ goldenVsText
        "validator arguments and budget"
        "test/Ual/Golden/validator-arguments.golden.json"
        (Text.decodeUtf8 (LBS.toStrict (encodeBlueprint contract)))
    ]

contract :: ContractBlueprint
contract =
  MkContractBlueprint
    { contractId = Just "ual-example"
    , contractPreamble =
        MkPreamble
          { preambleTitle = "UAL Example"
          , preambleDescription = Nothing
          , preambleVersion = "1.0.0"
          , preamblePlutusVersion = PlutusV3
          , preambleLicense = Nothing
          }
    , contractValidators =
        Set.singleton
          mkValidatorBlueprint
            { validatorId = Just "ticket-spend"
            , validatorTitle = "ticketSpend"
            , validatorRedeemer =
                MkArgumentBlueprint
                  { argumentTitle = Nothing
                  , argumentDescription = Nothing
                  , argumentPurpose = Set.singleton Purpose.Spend
                  , argumentSchema = definitionRef @Ticket
                  }
            , validatorArguments =
                [ MkAppliedArgument AsData (definitionRef @Ticket)
                , MkAppliedArgument AsScott (definitionRef @Integer)
                ]
            , validatorBudget = Just (MkExecutionBudget 1883313 12342)
            }
    , contractDefinitions = deriveDefinitions @[Ticket, Integer]
    }
```

Wire it into `plutus-tx/test/Ual/Spec.hs` and the cabal `other-modules`, as in
Task 1 Step 3.

- [ ] **Step 2: Run to verify failure**

Run: `cabal test plutus-tx:plutus-tx-test`
Expected: build failure, `Module 'PlutusTx.Blueprint.Validator' does not export 'AppliedArgument'`.

- [ ] **Step 3: Add the new blueprint types and fields**

In `plutus-tx/src/PlutusTx/Blueprint/Validator.hs`, add these types before
`ValidatorBlueprint`:

```haskell
{-| How an applied argument is serialised into a UPLC term.

Not part of CIP-0057: the blueprint's @datum@/@redeemer@/@parameters@ schemas say
what an argument *is*, not how it reaches the program. -}
data ArgumentEncoding = AsData | AsScott
  deriving stock (Show, Eq, Ord, Lift)

instance ToJSON ArgumentEncoding where
  toJSON = \case
    AsData -> "asData"
    AsScott -> "asScott"

-- | An on-chain execution budget, in Plutus cost-model units.
data ExecutionBudget = MkExecutionBudget
  { budgetCPU :: Integer
  , budgetMemory :: Integer
  }
  deriving stock (Show, Eq, Ord, Lift)

instance ToJSON ExecutionBudget where
  toJSON MkExecutionBudget {..} =
    buildObject $
      requiredField "exCPU" budgetCPU
        . requiredField "exMem" budgetMemory

{-| One element of a validator's ordered applied-argument list: the terms the
compiled program is applied to, in order. Positional — UAL's refined signature
gives argument types, not names. -}
data AppliedArgument (referencedTypes :: [Type]) = MkAppliedArgument
  { appliedArgumentEncoding :: ArgumentEncoding
  , appliedArgumentSchema :: Schema referencedTypes
  }
  deriving stock (Show, Eq, Ord)

instance ToJSON (AppliedArgument referencedTypes) where
  toJSON MkAppliedArgument {..} =
    buildObject $
      requiredField "encoding" appliedArgumentEncoding
        . requiredField "schema" appliedArgumentSchema
```

Add `import PlutusTx.Blueprint.Schema (Schema)`,
`import Language.Haskell.TH.Syntax (Lift)` and `{-# LANGUAGE LambdaCase #-}` if
not already present. `DeriveLift` is in the package's `default-extensions`, so no
pragma is needed for the deriving clauses. Both types have exported constructors,
so a stock `Lift` instance splices names that are in scope at the use site — the
reason `ResolvedArgument` cannot have one (Task 1 Step 2).

Add three fields to `ValidatorBlueprint`, after `validatorCompiled`:

```haskell
  , validatorId :: Maybe Text
  {-^ A stable identifier, unique within the contract, used to reference this
  validator from an assurance document. RECOMMENDED by the assurance CIP;
  emitted by the UAL producer. -}
  , validatorArguments :: [AppliedArgument referencedTypes]
  {-^ The ordered list of terms the compiled program is applied to. Empty when
  no UAL @ONCHAIN@ block describes this validator. -}
  , validatorBudget :: Maybe ExecutionBudget
  -- ^ The execution budget declared for this validator.
```

Extend its `ToJSON` instance's `buildObject` chain with:

```haskell
        . optionalField "id" validatorId
        . optionalField "arguments" (NE.nonEmpty validatorArguments)
        . optionalField "budget" validatorBudget
```

`NE` is already imported as `Data.List.NonEmpty qualified as NE`. Using
`NE.nonEmpty` mirrors how `parameters` is emitted, so an empty list omits the key
rather than writing `[]`.

Add the smart constructor at the end of the module:

```haskell
{-| A 'ValidatorBlueprint' with everything optional left out. Set the fields you
need with record-update syntax:

@
mkValidatorBlueprint
  { validatorTitle = "My Validator"
  , validatorRedeemer = …
  }
@

Prefer this over the raw constructor: new optional fields can then be added
without breaking your call site. -}
mkValidatorBlueprint :: ValidatorBlueprint referencedTypes
mkValidatorBlueprint =
  MkValidatorBlueprint
    { validatorTitle = ""
    , validatorDescription = Nothing
    , validatorRedeemer =
        error "mkValidatorBlueprint: validatorRedeemer must be set"
    , validatorDatum = Nothing
    , validatorParameters = []
    , validatorCompiled = Nothing
    , validatorId = Nothing
    , validatorArguments = []
    , validatorBudget = Nothing
    }
```

The `error` for `validatorRedeemer` is deliberate: CIP-0057 makes `redeemer`
required, so there is no honest default, and a bottom that names the missing
field is better than a silently wrong one.

- [ ] **Step 4: Add `Eq` and `Lift` to `PlutusVersion`**

In `plutus-tx/src/PlutusTx/Blueprint/PlutusVersion.hs`, change

```haskell
  deriving stock (Show)
```

to

```haskell
  deriving stock (Show, Eq, Lift)
```

and add `import Language.Haskell.TH.Syntax (Lift)`. `Eq` is needed by the
version-agreement check in Task 5; `Lift` by the TH splice in Task 8.

- [ ] **Step 5: Extend the JSON key order**

In `plutus-tx/src/PlutusTx/Blueprint/Write.hs`, extend the `Pretty.keyOrder`
list. Insert `"id"` before `"title"`, and add `"arguments"`, `"budget"`,
`"encoding"` after `"schema"`:

```haskell
            [ "$id"
            , "$schema"
            , "$vocabulary"
            , "preamble"
            , "validators"
            , "definitions"
            , "id"
            , "title"
            , "description"
            , "version"
            , "plutusVersion"
            , "license"
            , "redeemer"
            , "datum"
            , "parameters"
            , "arguments"
            , "budget"
            , "purpose"
            , "encoding"
            , "schema"
            ]
```

- [ ] **Step 6: Fix the two existing construction sites**

In `doc/docusaurus/static/code/Example/Cip57/Blueprint/Main.hs`, change
`myValidator = MkValidatorBlueprint { … }` to
`myValidator = mkValidatorBlueprint { … }` and drop the now-defaulted
`validatorCompiled = Nothing` line. Add `mkValidatorBlueprint` to the
`PlutusTx.Blueprint` import if the module imports names explicitly (it imports
the whole module, so no change).

In `plutus-tx-plugin/test/Blueprint/Tests.hs`, change each
`MkValidatorBlueprint { … }` to `mkValidatorBlueprint { … }` and add
`mkValidatorBlueprint` to the `PlutusTx.Blueprint.Validator` import list.

- [ ] **Step 7: Run to verify pass and inspect the golden file**

Run: `cabal test plutus-tx:plutus-tx-test`
Expected: PASS. `tasty-golden` creates
`plutus-tx/test/Ual/Golden/validator-arguments.golden.json` on the first run.

Open it and confirm the validator object contains, in this order: `id`, `title`,
`redeemer`, `arguments` (two entries, each with `encoding` then `schema`), and
`budget` with `exCPU` and `exMem`. If `arguments` is absent, `NE.nonEmpty` is
being applied to an empty list — check Step 3.

Then confirm the plugin tests still build:

Run: `cabal build plutus-tx-plugin:plutus-tx-test 2>&1 | tail -5`
Expected: no errors. (If the plugin test suite has a different target name, find
it with `cabal list-bin` or `grep '^test-suite' plutus-tx-plugin/*.cabal`.)

- [ ] **Step 8: Write the changelog fragment**

Look at an existing fragment for the exact format:

Run: `ls plutus-tx/changelog.d/ && cat plutus-tx/changelog.d/*.md | head -20`

Then create `plutus-tx/changelog.d/20260824_000000_ual_validator_fields.md`
following that format, with an `added` entry describing `validatorId`,
`validatorArguments`, `validatorBudget` and `mkValidatorBlueprint`, and a
`changed` entry noting that `MkValidatorBlueprint` gained three fields so
record-construction sites must be updated or switched to `mkValidatorBlueprint`.

- [ ] **Step 9: Commit**

```bash
git add plutus-tx plutus-tx-plugin/test/Blueprint/Tests.hs doc/docusaurus/static/code/Example/Cip57/Blueprint/Main.hs
git commit --no-verify -m "feat(plutus-tx): applied-argument encodings and budget on ValidatorBlueprint"
```

---

### Task 5: `attachUal`

**Files:**
- Create: `plutus-tx/src/PlutusTx/Ual/Resolve.hs`
- Create: `plutus-tx/test/Ual/Resolve/Spec.hs`
- Modify: `plutus-tx/plutus-tx.cabal`
- Modify: `plutus-tx/test/Ual/Spec.hs`

`attachUal` fills `validatorArguments` and `validatorBudget` on each validator
whose `validatorId` matches an `ONCHAIN` name, and reports the assembly-time
errors of spec §8.2 checks 3, 5 and 7.

**Id derivation.** `ualIdFor` (Task 8) and `attachUal` must agree, so the rule
lives here and Task 8 calls it. `onchainIdOf` is **identity** on the `ONCHAIN`
name: the author can then read the id straight off the annotation, and there is
one fewer transformation to get wrong.

**Where argument schemas come from.** `AppliedArgument` holds a
`Schema referencedTypes`, and the only way to build a `SchemaDefinitionRef` is
from a `DefinitionId`, which needs the *type* — not its name as text. `attachUal`
has only the name. That is why `OnchainDecl` carries `onchainResolvedArgs`,
filled by the TH splice (Task 8), which is the one place that has the type.
`attachUal` reads `onchainResolvedArgs` and ignores `onchainArgs`.

**Inspecting the result.** `ContractBlueprint` is existential, so you cannot
pattern-match a validator out of it and keep its `referencedTypes` index. Tests
therefore assert against `Aeson.toJSON` of the contract, which is what a caller
ultimately cares about anyway.

- [ ] **Step 1: Write the failing tests**

Create `plutus-tx/test/Ual/Resolve/Spec.hs`:

```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Ual.Resolve.Spec (tests) where

import Prelude

import Data.Aeson ((.=))
import Data.Aeson qualified as Aeson
import Data.Aeson.Key qualified as Key
import Data.Aeson.KeyMap qualified as KeyMap
import Data.Either (isRight)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Vector qualified as V
import GHC.Generics (Generic)
import PlutusTx.Blueprint.Argument (ArgumentBlueprint (..))
import PlutusTx.Blueprint.Contract (ContractBlueprint (..))
import PlutusTx.Blueprint.Definition (HasBlueprintDefinition, definitionRef, deriveDefinitions)
import PlutusTx.Blueprint.Definition.Unroll (definitionId)
import PlutusTx.Blueprint.PlutusVersion (PlutusVersion (..))
import PlutusTx.Blueprint.Preamble (Preamble (..))
import PlutusTx.Blueprint.Purpose qualified as Purpose
import PlutusTx.Blueprint.Schema (Schema)
import PlutusTx.Blueprint.Validator
  ( ExecutionBudget (..)
  , ValidatorBlueprint
  , mkValidatorBlueprint
  , validatorId
  , validatorRedeemer
  , validatorTitle
  )
import PlutusTx.Ual.Error (UalError (..))
import PlutusTx.Ual.Resolve (attachUal)
import PlutusTx.Ual.Syntax
  ( ArgumentEncoding (..)
  , ModuleUal (..)
  , OnchainDecl (..)
  , ResolvedArgument (..)
  , UalArgument (..)
  , UalModuleName (..)
  , emptyModuleUal
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))

newtype Ticket = MkTicket Integer
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)

tests :: TestTree
tests =
  testGroup
    "Resolve"
    [ testCase "fills arguments on the matching validator" $
        (>>= lookupKey "arguments") . firstValidator
          <$> attachUal [uals decl] (contract [validator (Just "v")])
          @?= Right
            ( Just
                ( Aeson.Array
                    ( V.fromList
                        [ Aeson.object ["encoding" .= ("asData" :: Text), "schema" .= ticketRef]
                        , Aeson.object ["encoding" .= ("asScott" :: Text), "schema" .= integerRef]
                        ]
                    )
                )
            )
    , testCase "fills the budget" $
        (>>= lookupKey "budget") . firstValidator
          <$> attachUal
            [uals decl {onchainBudget = Just (MkExecutionBudget 7 8)}]
            (contract [validator (Just "v")])
          @?= Right (Just (Aeson.object ["exCPU" .= (7 :: Integer), "exMem" .= (8 :: Integer)]))
    , testCase "no ONCHAIN blocks leaves the validator without arguments" $
        (>>= lookupKey "arguments") . firstValidator
          <$> attachUal [] (contract [validator (Just "v")])
          @?= Right Nothing
    , testCase "matching version is accepted" $
        assertBool "should succeed" . isRight $
          attachUal
            [uals decl {onchainVersion = Just PlutusV3}]
            (contract [validator (Just "v")])
    , testCase "version disagreement is reported" $
        attachUal
          [uals decl {onchainVersion = Just PlutusV2}]
          (contract [validator (Just "v")])
          @?= Left [VersionMismatch "v" "PlutusV2" "PlutusV3"]
    , testCase "ONCHAIN with no matching validator is reported" $
        attachUal [uals decl] (contract [validator (Just "other")])
          @?= Left [NoValidatorForOnchain "v"]
    , testCase "validator with no id and no ONCHAIN block is fine" $
        assertBool "should succeed" . isRight $ attachUal [] (contract [validator Nothing])
    , testCase "duplicate validator ids are reported" $
        attachUal [] (contract [validator (Just "dup"), validator2 (Just "dup")])
          @?= Left [DuplicateValidatorId "dup"]
    ]

decl :: OnchainDecl
decl =
  OnchainDecl
    { onchainName = "v"
    , onchainArgs = [UalArgument "Ticket" AsData, UalArgument "Integer" AsScott]
    , onchainResult = "()"
    , onchainVersion = Nothing
    , onchainBudget = Nothing
    , onchainLine = 1
    , onchainResolvedArgs =
        [ ResolvedArgument AsData (definitionId @Ticket)
        , ResolvedArgument AsScott (definitionId @Integer)
        ]
    }

uals :: OnchainDecl -> ModuleUal
uals d = (emptyModuleUal (UalModuleName "M")) {ualOnchain = [d]}

validator :: Maybe Text -> ValidatorBlueprint '[Ticket, Integer]
validator vid =
  mkValidatorBlueprint
    { validatorId = vid
    , validatorTitle = "first"
    , validatorRedeemer =
        MkArgumentBlueprint
          { argumentTitle = Nothing
          , argumentDescription = Nothing
          , argumentPurpose = Set.singleton Purpose.Spend
          , argumentSchema = definitionRef @Ticket
          }
    }

validator2 :: Maybe Text -> ValidatorBlueprint '[Ticket, Integer]
validator2 vid = (validator vid) {validatorTitle = "second"}

contract :: [ValidatorBlueprint '[Ticket, Integer]] -> ContractBlueprint
contract vs =
  MkContractBlueprint
    { contractId = Nothing
    , contractPreamble =
        MkPreamble
          { preambleTitle = "t"
          , preambleDescription = Nothing
          , preambleVersion = "1"
          , preamblePlutusVersion = PlutusV3
          , preambleLicense = Nothing
          }
    , contractValidators = Set.fromList vs
    , contractDefinitions = deriveDefinitions @[Ticket, Integer]
    }

{-| The first validator's JSON. @ContractBlueprint@ is existential, so this is
the only index-agnostic way to look inside it. -}
firstValidator :: ContractBlueprint -> Maybe Aeson.Value
firstValidator bp = case Aeson.toJSON bp of
  Aeson.Object o -> case KeyMap.lookup "validators" o of
    Just (Aeson.Array vs) | not (V.null vs) -> Just (vs V.! 0)
    _ -> Nothing
  _ -> Nothing

lookupKey :: Text -> Aeson.Value -> Maybe Aeson.Value
lookupKey k = \case
  Aeson.Object o -> KeyMap.lookup (Key.fromText k) o
  _ -> Nothing

ticketRef, integerRef :: Aeson.Value
ticketRef = Aeson.toJSON (definitionRef @Ticket :: Schema '[Ticket, Integer])
integerRef = Aeson.toJSON (definitionRef @Integer :: Schema '[Ticket, Integer])
```

Two things to check while writing this:

- `definitionId` is a `HasBlueprintDefinition` class method declared in
  `PlutusTx.Blueprint.Definition.Unroll` and re-exported by
  `PlutusTx.Blueprint.Definition`. Import it from the latter, alongside
  `definitionRef` and `deriveDefinitions`, and drop the separate
  `PlutusTx.Blueprint.Definition.Unroll` import from the list above.
- Add `vector` to the test suite's `build-depends`.

Note the "duplicate validator ids" case relies on `validatorTitle` differing
("first" vs "second"), because `contractValidators` is a `Set` ordered by the
derived `Ord`, which starts at the title. Two validators identical but for their
id would collapse into one set element and the test would not exercise anything.

Wire `Ual.Resolve.Spec` into `Ual.Spec` and the cabal `other-modules`.

- [ ] **Step 2: Run to verify failure**

Run: `cabal test plutus-tx:plutus-tx-test`
Expected: build failure, `Could not find module 'PlutusTx.Ual.Resolve'`.

- [ ] **Step 3: Implement `attachUal`**

Create `plutus-tx/src/PlutusTx/Ual/Resolve.hs`:

```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
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
import PlutusTx.Ual.Syntax (ModuleUal (..), OnchainDecl (..), ResolvedArgument (..))

{-| The blueprint validator id an @ONCHAIN@ block claims. Identity, so the id is
readable straight off the annotation. 'PlutusTx.Ual.TH.ualIdFor' must agree. -}
onchainIdOf :: OnchainDecl -> Text
onchainIdOf = onchainName

{-| Attach the UAL interface facts to a blueprint: fill @arguments@ and @budget@
on every validator whose 'validatorId' matches an @ONCHAIN@ name.

Reports every error it finds rather than stopping at the first, so one run tells
the author everything that is wrong. -}
attachUal :: [ModuleUal] -> ContractBlueprint -> Either [UalError] ContractBlueprint
attachUal modules MkContractBlueprint {..} =
  case sort (dupIdErrors <> versionErrors <> missingErrors <> orphanErrors) of
    [] -> Right MkContractBlueprint {contractValidators = Set.map fill contractValidators, ..}
    errs -> Left errs
  where
    preambleVersion' = preamblePlutusVersion contractPreamble

    decls :: Map.Map Text OnchainDecl
    decls = Map.fromList [(onchainIdOf d, d) | m <- modules, d <- ualOnchain m]

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

    fill v = case validatorId v >>= \vid -> Map.lookup vid decls of
      Nothing -> v
      Just d ->
        v
          { validatorArguments = toApplied <$> onchainResolvedArgs d
          , validatorBudget = onchainBudget d
          }

    toApplied r =
      MkAppliedArgument
        { appliedArgumentEncoding = resolvedEncoding r
        , appliedArgumentSchema = SchemaDefinitionRef (resolvedDefinitionId r)
        }

renderVersion :: PlutusVersion -> Text
renderVersion = Text.pack . show
```

Two notes on this code:

- It uses `onchainResolvedArgs`, not `onchainArgs`. A blueprint built from a
  parser-only `OnchainDecl` (no TH) therefore gets an empty `arguments` list,
  which the JSON encoder omits. That is the honest outcome: without the TH splice
  there are no definition ids to reference.
- `Set.map fill` needs `Ord (ValidatorBlueprint referencedTypes)`, which is
  derived. `Set.map` collapses equal results, but `fill` never touches
  `validatorTitle`, which is the first `Ord` field, so distinct validators stay
  distinct. Do not generalise `fill` to change the title.

Add `PlutusTx.Ual.Resolve` to the library's `exposed-modules`.

- [ ] **Step 4: Run to verify pass**

Run: `cabal run plutus-tx:plutus-tx-test -- -p '/Resolve/'`
Expected: PASS, 8 tests.

- [ ] **Step 5: Commit**

```bash
git add plutus-tx
git commit --no-verify -m "feat(plutus-tx): attachUal fills applied arguments from ONCHAIN blocks"
```

---

### Task 6: Assurance document types and writer

**Files:**
- Create: `plutus-tx/src/PlutusTx/Assurance/Document.hs`
- Create: `plutus-tx/src/PlutusTx/Assurance/Write.hs`
- Create: `plutus-tx/src/PlutusTx/Assurance.hs`
- Create: `plutus-tx/test/Ual/Assurance/Spec.hs`
- Create: `plutus-tx/test/Ual/Golden/assurance.golden.json`
- Modify: `plutus-tx/plutus-tx.cabal`
- Modify: `plutus-tx/test/Ual/Spec.hs`

- [ ] **Step 1: Write the failing golden test**

Create `plutus-tx/test/Ual/Assurance/Spec.hs`:

```haskell
{-# LANGUAGE OverloadedStrings #-}

module Ual.Assurance.Spec (tests) where

import Prelude

import Data.ByteString.Lazy qualified as LBS
import Data.Text.Encoding qualified as Text
import PlutusTx.Assurance
  ( AssuranceDocument (..)
  , AssurancePreamble (..)
  , BlueprintRef (..)
  , Digest (..)
  , FormalFragment (..)
  , FormalStatement (..)
  , Property (..)
  , RegistryEntry (..)
  , Statement (..)
  , encodeAssurance
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Extras (goldenVsText)

tests :: TestTree
tests =
  testGroup
    "Assurance"
    [ goldenVsText
        "document"
        "test/Ual/Golden/assurance.golden.json"
        (Text.decodeUtf8 (LBS.toStrict (encodeAssurance doc)))
    ]

doc :: AssuranceDocument
doc =
  MkAssuranceDocument
    { assurancePreamble =
        MkAssurancePreamble
          { assuranceTitle = "Ticket contract — UAL assurance"
          , assuranceDescription = Just "Generated from UAL annotations."
          , assuranceVersion = Just "1.0.0"
          , assuranceAuthors = ["Example Author <a@example.com>"]
          , assuranceCreated = "2026-08-24"
          , assuranceLicense = Just "CC-BY-4.0"
          }
    , assuranceBlueprint =
        MkBlueprintRef
          { blueprintUri = "plutus.json"
          , blueprintHash = Just (MkDigest "sha256" "0f")
          }
    , assuranceLanguages =
        [ ( "ual"
          , MkRegistryEntry
              { registryName = "Universal Annotation Language"
              , registryVersion = "0.4"
              , registryUri = Just "https://github.com/input-output-hk/ual-spec"
              , registryDescription = Nothing
              }
          )
        ]
    , assuranceTools = []
    , assuranceFormalFragments =
        [ MkFormalFragment
            { fragmentId = "My.Contract"
            , fragmentLanguage = "ual"
            , fragmentImports = ["My.Types"]
            , fragmentSource = "def ok : Prop := True"
            }
        ]
    , assuranceProperties =
        [ MkProperty
            { propertyIdent = "ticket_ok"
            , propertyTitle = Nothing
            , propertyValidators = ["ticket-spend"]
            , propertyStatement =
                MkStatement
                  { statementText = "A valid ticket is always accepted."
                  , statementFormal =
                      Just
                        MkFormalStatement
                          { formalLanguage = "ual"
                          , formalUses = ["My.Contract"]
                          , formalSource = "\8704 t, ok t"
                          }
                  }
            }
        ]
    }
```

Wire into `Ual.Spec` and the cabal stanzas as before.

- [ ] **Step 2: Run to verify failure**

Run: `cabal test plutus-tx:plutus-tx-test`
Expected: build failure, `Could not find module 'PlutusTx.Assurance'`.

- [ ] **Step 3: Implement the document types**

Create `plutus-tx/src/PlutusTx/Assurance/Document.hs`:

```haskell
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

{-| Types for the assurance document defined by the Plutus Blueprint Assurance
Documents CIP: a standalone JSON document publishing behavioural claims about the
validators of a CIP-0057 blueprint.

Two fields are extensions this producer needs and the CIP adds:
'assuranceFormalFragments' (named, importable blocks of formal definitions) and
'formalUses' (which fragments a statement elaborates against). The CIP's
meta-schema sets no @additionalProperties: false@, so a document carrying them
validates against the published schema as-is. -}
module PlutusTx.Assurance.Document where

import Prelude

import Data.Aeson (ToJSON (..))
import Data.Aeson qualified as Aeson
import Data.Aeson.Extra (buildObject, optionalField, requiredField)
import Data.Aeson.Key qualified as Key
import Data.Aeson.KeyMap qualified as KeyMap
import Data.List.NonEmpty qualified as NE
import Data.Text (Text)

schemaUri :: Text
schemaUri = "https://cips.cardano.org/cips/cipXXXX/schemas/assurance.json"

data AssuranceDocument = MkAssuranceDocument
  { assurancePreamble :: AssurancePreamble
  , assuranceBlueprint :: BlueprintRef
  , assuranceLanguages :: [(Text, RegistryEntry)]
  , assuranceTools :: [(Text, RegistryEntry)]
  , assuranceFormalFragments :: [FormalFragment]
  , assuranceProperties :: [Property]
  }
  deriving stock (Eq, Show)

instance ToJSON AssuranceDocument where
  toJSON MkAssuranceDocument {..} =
    buildObject $
      requiredField "$schema" schemaUri
        . requiredField "preamble" assurancePreamble
        . requiredField "blueprint" assuranceBlueprint
        . optionalField "languages" (registry assuranceLanguages)
        . optionalField "tools" (registry assuranceTools)
        . optionalField "formalFragments" (NE.nonEmpty assuranceFormalFragments)
        . requiredField "properties" assuranceProperties
    where
      registry [] = Nothing
      registry kvs =
        Just . Aeson.Object . KeyMap.fromList $
          [(Key.fromText k, toJSON v) | (k, v) <- kvs]

data AssurancePreamble = MkAssurancePreamble
  { assuranceTitle :: Text
  , assuranceDescription :: Maybe Text
  , assuranceVersion :: Maybe Text
  , assuranceAuthors :: [Text]
  , assuranceCreated :: Text
  -- ^ @YYYY-MM-DD@. The CIP's schema enforces the shape.
  , assuranceLicense :: Maybe Text
  }
  deriving stock (Eq, Show)

instance ToJSON AssurancePreamble where
  toJSON MkAssurancePreamble {..} =
    buildObject $
      requiredField "title" assuranceTitle
        . requiredField "authors" assuranceAuthors
        . requiredField "created" assuranceCreated
        . optionalField "description" assuranceDescription
        . optionalField "version" assuranceVersion
        . optionalField "license" assuranceLicense

data BlueprintRef = MkBlueprintRef
  { blueprintUri :: Text
  , blueprintHash :: Maybe Digest
  }
  deriving stock (Eq, Show)

instance ToJSON BlueprintRef where
  toJSON MkBlueprintRef {..} =
    buildObject $
      requiredField "uri" blueprintUri
        . optionalField "hash" blueprintHash

data Digest = MkDigest
  { digestAlg :: Text
  , digestValue :: Text
  -- ^ Lowercase hex.
  }
  deriving stock (Eq, Show)

instance ToJSON Digest where
  toJSON MkDigest {..} =
    buildObject $
      requiredField "alg" digestAlg
        . requiredField "digest" digestValue

data RegistryEntry = MkRegistryEntry
  { registryName :: Text
  , registryVersion :: Text
  , registryUri :: Maybe Text
  , registryDescription :: Maybe Text
  }
  deriving stock (Eq, Show)

instance ToJSON RegistryEntry where
  toJSON MkRegistryEntry {..} =
    buildObject $
      requiredField "name" registryName
        . requiredField "version" registryVersion
        . optionalField "uri" registryUri
        . optionalField "description" registryDescription

{-| A named block of formal definitions. The id is the surface module name, and
'fragmentImports' mirror that module's imports restricted to modules that also
produced a fragment. -}
data FormalFragment = MkFormalFragment
  { fragmentId :: Text
  , fragmentLanguage :: Text
  , fragmentImports :: [Text]
  , fragmentSource :: Text
  }
  deriving stock (Eq, Show)

instance ToJSON FormalFragment where
  toJSON MkFormalFragment {..} =
    buildObject $
      requiredField "id" fragmentId
        . requiredField "language" fragmentLanguage
        . optionalField "imports" (NE.nonEmpty fragmentImports)
        . requiredField "source" fragmentSource

data Property = MkProperty
  { propertyIdent :: Text
  , propertyTitle :: Maybe Text
  , propertyValidators :: [Text]
  , propertyStatement :: Statement
  }
  deriving stock (Eq, Show)

instance ToJSON Property where
  toJSON MkProperty {..} =
    buildObject $
      requiredField "id" propertyIdent
        . requiredField "scope" (Aeson.object ["validators" Aeson..= propertyValidators])
        . requiredField "statement" propertyStatement
        . optionalField "title" propertyTitle

data Statement = MkStatement
  { statementText :: Text
  , statementFormal :: Maybe FormalStatement
  }
  deriving stock (Eq, Show)

instance ToJSON Statement where
  toJSON MkStatement {..} =
    buildObject $
      requiredField "text" statementText
        . optionalField "formal" statementFormal

data FormalStatement = MkFormalStatement
  { formalLanguage :: Text
  , formalUses :: [Text]
  , formalSource :: Text
  }
  deriving stock (Eq, Show)

instance ToJSON FormalStatement where
  toJSON MkFormalStatement {..} =
    buildObject $
      requiredField "language" formalLanguage
        . requiredField "source" formalSource
        . optionalField "uses" (NE.nonEmpty formalUses)
```

- [ ] **Step 4: Implement the writer**

Create `plutus-tx/src/PlutusTx/Assurance/Write.hs`:

```haskell
{-# LANGUAGE OverloadedStrings #-}

module PlutusTx.Assurance.Write
  ( encodeAssurance
  , writeAssurance
  , blueprintRef
  ) where

import Prelude

import Data.Aeson (toJSON)
import Data.Aeson.Encode.Pretty (encodePretty')
import Data.Aeson.Encode.Pretty qualified as Pretty
import Data.ByteString qualified as BS
import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Lazy qualified as LBS
import Data.Text (Text)
import Data.Text.Encoding qualified as Text
import PlutusCore.Crypto.Hash (sha2_256)
import PlutusTx.Assurance.Document (AssuranceDocument, BlueprintRef (..), Digest (..))

writeAssurance :: FilePath -> AssuranceDocument -> IO ()
writeAssurance f = LBS.writeFile f . encodeAssurance

encodeAssurance :: AssuranceDocument -> LBS.ByteString
encodeAssurance =
  encodePretty'
    Pretty.defConfig
      { Pretty.confIndent = Pretty.Spaces 2
      , Pretty.confCompare =
          Pretty.keyOrder
            [ "$schema"
            , "preamble"
            , "blueprint"
            , "languages"
            , "tools"
            , "formalFragments"
            , "properties"
            , "id"
            , "title"
            , "description"
            , "version"
            , "authors"
            , "created"
            , "license"
            , "uri"
            , "hash"
            , "alg"
            , "digest"
            , "language"
            , "imports"
            , "uses"
            , "source"
            , "scope"
            , "validators"
            , "statement"
            , "text"
            , "formal"
            ]
      , Pretty.confNumFormat = Pretty.Generic
      , Pretty.confTrailingNewline = True
      }
    . toJSON

{-| Build the blueprint reference for an already-written @plutus.json@, hashing
the bytes on disk.

Order matters: the CIP requires the digest to be over the blueprint document
exactly as retrieved, so this must run *after* 'PlutusTx.Blueprint.writeBlueprint'
and before 'writeAssurance'. -}
blueprintRef :: Text -> FilePath -> IO BlueprintRef
blueprintRef uri path = do
  bytes <- BS.readFile path
  pure
    MkBlueprintRef
      { blueprintUri = uri
      , blueprintHash =
          Just (MkDigest "sha256" (Text.decodeUtf8 (Base16.encode (sha2_256 bytes))))
      }
```

**On the hashing:** `PlutusCore.Crypto.Hash` already exports `sha2_256`, next to
the `blake2b_224` that `PlutusTx.Blueprint.Validator` imports from it, and
`base16-bytestring` is already a `plutus-tx` library dependency. **Add no new
package** — in particular do not reach for `cryptohash-sha256` or `crypton`.

Create `plutus-tx/src/PlutusTx/Assurance.hs`:

```haskell
module PlutusTx.Assurance (module X) where

import PlutusTx.Assurance.Document as X
import PlutusTx.Assurance.Write as X
```

Add all three modules to `exposed-modules`. No `build-depends` change is needed:
`aeson-pretty`, `base16-bytestring`, `bytestring` and `text` are all already
`plutus-tx` library dependencies.

- [ ] **Step 5: Run to verify pass and inspect the golden file**

Run: `cabal test plutus-tx:plutus-tx-test`
Expected: PASS, with `plutus-tx/test/Ual/Golden/assurance.golden.json` created.

Open it and check: `$schema` first, `formalFragments` before `properties`, the
fragment carries `imports`, the property's `formal` carries `uses`, and no key
holds `[]`.

- [ ] **Step 6: Commit**

```bash
git add plutus-tx
git commit --no-verify -m "feat(plutus-tx): assurance document types and writer"
```

---

### Task 7: `buildAssurance`

**Files:**
- Create: `plutus-tx/src/PlutusTx/Assurance/Build.hs`
- Modify: `plutus-tx/src/PlutusTx/Assurance.hs`
- Modify: `plutus-tx/test/Ual/Assurance/Spec.hs`
- Modify: `plutus-tx/plutus-tx.cabal`

- [ ] **Step 1: Write the failing tests**

Add to `plutus-tx/test/Ual/Assurance/Spec.hs` a `buildTests` group, added to the
top-level `tests` list. Extend the imports with `buildAssurance`,
`PlutusTx.Ual.Syntax (ModuleUal (..), PropertyDecl (..), UalModuleName (..), emptyModuleUal)`,
`PlutusTx.Ual.Error (UalError (..))`, and `Test.Tasty.HUnit (testCase, (@?=))`.

```haskell
buildTests :: TestTree
buildTests =
  testGroup
    "buildAssurance"
    [ testCase "a module with no predicates produces no fragment" $
        (fmap fragmentId . assuranceFormalFragments)
          <$> build [modWith "A" [] [prop "p"]]
          @?= Right []
    , testCase "a property in a module with no fragment uses nothing" $
        (concatMap uses . assuranceProperties) <$> build [modWith "A" [] [prop "p"]]
          @?= Right []
    , testCase "a property in a module with a fragment uses that fragment" $
        (concatMap uses . assuranceProperties) <$> build [modWith "A" ["def a := 1"] [prop "p"]]
          @?= Right ["A"]
    , testCase "predicates are joined in source order, blank line separated" $
        (fmap fragmentSource . assuranceFormalFragments)
          <$> build [modWith "A" ["one", "two"] []]
          @?= Right ["one\n\ntwo"]
    , testCase "imports are restricted to modules that produced a fragment" $
        (fmap fragmentImports . assuranceFormalFragments)
          <$> build
            [ (modWith "A" ["a"] []) {ualModuleImports = map UalModuleName ["B", "C", "Data.Text"]}
            , modWith "B" ["b"] []
            , modWith "C" [] []
            ]
          @?= Right [["B"], []]
    , testCase "duplicate property ids are reported" $
        build [modWith "A" [] [prop "p"], modWith "B" [] [prop "p"]]
          @?= Left [DuplicatePropertyId "p"]
    , testCase "a fragment import cycle is reported" $
        build
          [ (modWith "A" ["a"] []) {ualModuleImports = [UalModuleName "B"]}
          , (modWith "B" ["b"] []) {ualModuleImports = [UalModuleName "A"]}
          ]
          @?= Left [FragmentCycle ["A", "B"]]
    ]
  where
    build ms = buildAssurance pre ref "ticket-spend" ms
    pre = assurancePreamble doc
    ref = assuranceBlueprint doc
    uses p = maybe [] formalUses (statementFormal (propertyStatement p))
    modWith n preds props =
      (emptyModuleUal (UalModuleName n))
        { ualPredicates = preds
        , ualProperties = props
        }
    prop n = PropertyDecl {propertyName = n, propertyText = "t", propertyBody = "True", propertyLine = 1}
```

- [ ] **Step 2: Run to verify failure**

Run: `cabal test plutus-tx:plutus-tx-test`
Expected: build failure, `Variable not in scope: buildAssurance`.

- [ ] **Step 3: Implement `buildAssurance`**

Create `plutus-tx/src/PlutusTx/Assurance/Build.hs`:

```haskell
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusTx.Assurance.Build
  ( buildAssurance
  , ualLanguageKey
  ) where

import Prelude

import Data.List (sort)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import PlutusTx.Assurance.Document
import PlutusTx.Ual.Error (UalError (..))
import PlutusTx.Ual.Syntax
  ( ModuleUal (..)
  , PropertyDecl (..)
  , UalModuleName (..)
  )

-- | The @languages@ registry key this producer uses.
ualLanguageKey :: Text
ualLanguageKey = "ual"

{-| Assemble an assurance document from the UAL of every annotated module.

Properties carry no evidence records: this runs at build time, before any proof.
The CIP names that state explicitly — a property with no evidence is "a stated,
unverified claim … a machine-readable specification target".

All properties are scoped to @defaultValidator@. Per-property scoping needs a
@scope@ field in the UAL @PROPERTY@ syntax, which does not exist yet; a single
scope is honest about what the annotation actually says. -}
buildAssurance
  :: AssurancePreamble
  -> BlueprintRef
  -> Text
  -- ^ The validator id every property is scoped to.
  -> [ModuleUal]
  -> Either [UalError] AssuranceDocument
buildAssurance preamble ref defaultValidator modules =
  case sort (dupPropertyErrors <> cycleErrors) of
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

    -- Only modules with at least one PREDICATE block become fragments.
    fragmentModules :: [ModuleUal]
    fragmentModules = [m | m <- modules, not (null (ualPredicates m))]

    fragmentIds :: Set Text
    fragmentIds = Set.fromList (nameOf . ualModuleName <$> fragmentModules)

    fragments =
      [ MkFormalFragment
        { fragmentId = nameOf (ualModuleName m)
        , fragmentLanguage = ualLanguageKey
        , fragmentImports =
            [ i
            | imp <- ualModuleImports m
            , let i = nameOf imp
            , Set.member i fragmentIds
            ]
        , fragmentSource = Text.intercalate "\n\n" (Text.strip <$> ualPredicates m)
        }
      | m <- fragmentModules
      ]

    properties =
      [ MkProperty
        { propertyIdent = propertyName p
        , propertyTitle = Nothing
        , propertyValidators = [defaultValidator]
        , propertyStatement =
            MkStatement
              { statementText = propertyText p
              , statementFormal =
                  Just
                    MkFormalStatement
                      { formalLanguage = ualLanguageKey
                      , formalUses =
                          [ nameOf (ualModuleName m)
                          | Set.member (nameOf (ualModuleName m)) fragmentIds
                          ]
                      , formalSource = propertyBody p
                      }
              }
        }
      | m <- modules
      , p <- ualProperties m
      ]

    dupPropertyErrors =
      [ DuplicatePropertyId pid
      | (pid, n) <-
          Map.toList
            (Map.fromListWith (+) [(propertyName p, 1 :: Int) | m <- modules, p <- ualProperties m])
      , n > 1
      ]

    -- Any strongly connected component of size > 1, reported once, sorted.
    cycleErrors = case findCycle edges of
      Nothing -> []
      Just c -> [FragmentCycle (sort c)]

    edges = Map.fromList [(fragmentId f, fragmentImports f) | f <- fragments]

ualRegistryEntry :: RegistryEntry
ualRegistryEntry =
  MkRegistryEntry
    { registryName = "Universal Annotation Language"
    , registryVersion = "0.4"
    , registryUri = Just "https://github.com/input-output-hk/ual-spec"
    , registryDescription = Just "Property specification language used by Blaster."
    }

{-| Find one cycle in a small dependency graph, by depth-first search with a
path stack. Returns the nodes on the cycle. -}
findCycle :: Map.Map Text [Text] -> Maybe [Text]
findCycle g = go (Map.keys g) Set.empty
  where
    go [] _ = Nothing
    go (n : ns) done
      | Set.member n done = go ns done
      | otherwise = case visit n [] done of
          Left cyc -> Just cyc
          Right done' -> go ns done'

    visit n path done
      | n `elem` path = Left (dropWhile (/= n) (reverse (n : path)))
      | Set.member n done = Right done
      | otherwise =
          case foldl step (Right done) (Map.findWithDefault [] n g) of
            Left cyc -> Left cyc
            Right done' -> Right (Set.insert n done')
      where
        step (Left cyc) _ = Left cyc
        step (Right d) m = visit m (n : path) d
```

Add `import PlutusTx.Assurance.Build as X` to `plutus-tx/src/PlutusTx/Assurance.hs`
and `PlutusTx.Assurance.Build` to `exposed-modules`.

- [ ] **Step 4: Run to verify pass**

Run: `cabal run plutus-tx:plutus-tx-test -- -p '/buildAssurance/'`
Expected: PASS, 7 tests.

If "a fragment import cycle is reported" fails with the nodes in the wrong order,
`findCycle` returned them rotated; the `sort` in `cycleErrors` normalises that,
so check that `sort` is actually applied.

- [ ] **Step 5: Commit**

```bash
git add plutus-tx
git commit --no-verify -m "feat(plutus-tx): buildAssurance assembles fragments and properties"
```

---

### Task 8: The Template Haskell adapter

**Files:**
- Create: `plutus-tx/src/PlutusTx/Ual/TH.hs`
- Create: `plutus-tx/src/PlutusTx/Ual.hs`
- Create: `plutus-tx/test/Ual/Fixture.hs`
- Modify: `plutus-tx/test/Ual/Spec.hs`
- Modify: `plutus-tx/plutus-tx.cabal`

Three constraints shape this module. Read them before writing code.

1. **`$(ualModule)` must be the last declaration.** TH `reify` and
   `lookupValueName` only see bindings from an *earlier* declaration group, so a
   splice above an `ONCHAIN` function cannot resolve it.
2. **`definitionId @T` must be spliced, not evaluated.** TH cannot run code that
   depends on instances defined in the module being compiled, and `T` usually is.
   So the splice *builds the expression* `definitionId @T` and the compiler
   evaluates it at runtime.
3. **`OnchainDecl`, `ResolvedArgument` and `ModuleUal` have no `Lift`
   instance** (Task 1 Step 2), because `DefinitionId`'s constructor is not
   exported. So those three are constructed as expressions, field by field, while
   their leaf fields are `lift`ed normally.

- [ ] **Step 1: Write the failing fixture test**

Create `plutus-tx/test/Ual/Fixture.hs`. Write the `∀` in the `PROPERTY` block as
a real Unicode character, not an escape.

```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

{-| A module with real UAL annotations, used to test that @$(ualModule)@ reads
its own source. Everything here is a fixture; nothing is a real contract. -}
module Ual.Fixture (Ticket (..), fixtureUal, fixtureContract, tests) where

import Prelude

import Data.Set qualified as Set
import Data.Text qualified as Text
import GHC.Generics (Generic)
import PlutusTx.Blueprint.Argument (ArgumentBlueprint (..))
import PlutusTx.Blueprint.Contract (ContractBlueprint (..))
import PlutusTx.Blueprint.Definition (HasBlueprintDefinition, definitionRef, deriveDefinitions)
import PlutusTx.Blueprint.PlutusVersion (PlutusVersion (..))
import PlutusTx.Blueprint.Preamble (Preamble (..))
import PlutusTx.Blueprint.Purpose qualified as Purpose
import PlutusTx.Blueprint.Validator
  ( ExecutionBudget (..)
  , mkValidatorBlueprint
  , validatorId
  , validatorRedeemer
  , validatorTitle
  )
import PlutusTx.Ual
  ( ModuleUal (..)
  , OnchainDecl (..)
  , PropertyDecl (..)
  , UalModuleName (..)
  )
import PlutusTx.Ual.TH (ualIdFor, ualModule)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

newtype Ticket = MkTicket Integer
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)

{-@ UPLC_DATA Ticket @-}

{-@ PREDICATE
def ticketOk (t : Ticket) : Prop := t.value > 0
@-}

{-@ ONCHAIN [version: PlutusV3] [exCPU: 1883313, exMem: 12342]
    ticketSpend :: { Ticket : asData }
                -> { [Integer] : asData }
                -> ()
@-}
ticketSpend :: Ticket -> [Integer] -> ()
ticketSpend _ _ = ()

{-@ PROPERTY ticket_ok
      "A ticket with a positive value is accepted."
    : ∀ (t : Ticket), ticketOk t
@-}

fixtureContract :: ContractBlueprint
fixtureContract =
  MkContractBlueprint
    { contractId = Just "ual-fixture"
    , contractPreamble =
        MkPreamble
          { preambleTitle = "UAL Fixture"
          , preambleDescription = Nothing
          , preambleVersion = "1.0.0"
          , preamblePlutusVersion = PlutusV3
          , preambleLicense = Nothing
          }
    , contractValidators =
        Set.singleton
          mkValidatorBlueprint
            { validatorId = Just $(ualIdFor 'ticketSpend)
            , validatorTitle = "ticketSpend"
            , validatorRedeemer =
                MkArgumentBlueprint
                  { argumentTitle = Nothing
                  , argumentDescription = Nothing
                  , argumentPurpose = Set.singleton Purpose.Spend
                  , argumentSchema = definitionRef @Ticket
                  }
            }
    , contractDefinitions = deriveDefinitions @[Ticket, [Integer]]
    }

-- Must be the last declaration: see constraint 1 above.
fixtureUal :: ModuleUal
fixtureUal = $(ualModule)

tests :: TestTree
tests =
  testGroup
    "TH"
    [ testCase "module name comes from the source header" $
        ualModuleName fixtureUal @?= UalModuleName "Ual.Fixture"
    , testCase "one ONCHAIN block, with its budget" $
        (onchainName <$> ualOnchain fixtureUal, onchainBudget <$> ualOnchain fixtureUal)
          @?= (["ticketSpend"], [Just (MkExecutionBudget 1883313 12342)])
    , testCase "the declared version survives" $
        (onchainVersion <$> ualOnchain fixtureUal) @?= [Just PlutusV3]
    , testCase "two resolved arguments, the second a list type" $
        (length . onchainResolvedArgs <$> ualOnchain fixtureUal) @?= [2]
    , testCase "one predicate, verbatim" $
        (Text.strip <$> ualPredicates fixtureUal)
          @?= ["def ticketOk (t : Ticket) : Prop := t.value > 0"]
    , testCase "one property, with its natural-language text" $
        (propertyText <$> ualProperties fixtureUal)
          @?= ["A ticket with a positive value is accepted."]
    , testCase "one UPLC_DATA type" $
        ualUplcData fixtureUal @?= ["Ticket"]
    , testCase "ualIdFor agrees with the ONCHAIN name" $
        $(ualIdFor 'ticketSpend) @?= ("ticketSpend" :: Text.Text)
    ]
```

Note `fixtureContract` sits *above* `fixtureUal` but *below* `ticketSpend`, which
is what `$(ualIdFor 'ticketSpend)` needs. `fixtureContract` is used by Task 9.

Wire `Ual.Fixture.tests` into `Ual.Spec` and `Ual.Fixture` into `other-modules`.

- [ ] **Step 2: Run to verify failure**

Run: `cabal test plutus-tx:plutus-tx-test`
Expected: build failure, `Could not find module 'PlutusTx.Ual.TH'`.

- [ ] **Step 3: Implement the TH adapter**

Create `plutus-tx/src/PlutusTx/Ual/TH.hs`:

```haskell
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

{-| Extract a module's UAL annotations at compile time.

The splice reads the enclosing module's own source file rather than GHC's comment
stream: @TH.location@ names the original @.hs@ path, and reading it needs no
exact-print annotations, no @Opt_KeepRawTokenStream@, and no dependence on how
GHC attaches comments to declarations. -}
module PlutusTx.Ual.TH
  ( ualModule
  , ualIdFor
  ) where

import Prelude

import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import Language.Haskell.TH qualified as TH
import Language.Haskell.TH.Syntax (addDependentFile, lift)
import PlutusTx.Blueprint.Definition.Unroll (definitionId)
import PlutusTx.Ual.Error (UalError (..), renderUalError)
import PlutusTx.Ual.Parser (moduleUalFromSource)
import PlutusTx.Ual.Syntax
  ( ModuleUal (..)
  , OnchainDecl (..)
  , ResolvedArgument (..)
  , UalArgument (..)
  , UalModuleName (..)
  )

{-| Read the enclosing module's own source, extract its UAL blocks, resolve every
@ONCHAIN@ and @UPLC_DATA@ name, and splice in the resulting 'ModuleUal'.

Place this splice **after** every @ONCHAIN@ function and @UPLC_DATA@ type in the
module: TH name lookup only sees bindings from an earlier declaration group.

@addDependentFile@ makes editing an annotation force a rebuild.

UAL blocks inside @#ifdef@ are read regardless of which branch CPP takes; blocks
under CPP are unsupported. -}
ualModule :: TH.Q TH.Exp
ualModule = do
  loc <- TH.location
  let path = TH.loc_filename loc
      fallback = UalModuleName (Text.pack (TH.loc_module loc))
  addDependentFile path
  src <- TH.runIO (Text.readFile path)
  m <- either die pure (moduleUalFromSource fallback src)
  mapM_ checkUplcData (ualUplcData m)
  onchainExps <- traverse onchainExp (ualOnchain m)
  [|
    ModuleUal
      { ualModuleName = $(lift (ualModuleName m))
      , ualModuleImports = $(lift (ualModuleImports m))
      , ualOnchain = $(pure (TH.ListE onchainExps))
      , ualPredicates = $(lift (ualPredicates m))
      , ualProperties = $(lift (ualProperties m))
      , ualUplcData = $(lift (ualUplcData m))
      }
    |]

{-| The blueprint validator id for an @ONCHAIN@ function, as a 'Text' expression.
Agrees with 'PlutusTx.Ual.Resolve.onchainIdOf', which is identity on the name.

Use it instead of writing the id as a string literal: the annotation and the
blueprint entry then cannot drift, and a renamed function is a compile error
rather than a silently unmatched id. -}
ualIdFor :: TH.Name -> TH.Q TH.Exp
ualIdFor n = lift (Text.pack (TH.nameBase n))

----------------------------------------------------------------------------------------------------

{-| An 'OnchainDecl' as an expression: leaf fields lifted, @onchainResolvedArgs@
built from @definitionId \@T@ calls the compiler evaluates. -}
onchainExp :: OnchainDecl -> TH.Q TH.Exp
onchainExp d = do
  checkOnchain d
  args <- traverse resolvedArgExp (onchainArgs d)
  [|
    OnchainDecl
      { onchainName = $(lift (onchainName d))
      , onchainArgs = $(lift (onchainArgs d))
      , onchainResult = $(lift (onchainResult d))
      , onchainVersion = $(lift (onchainVersion d))
      , onchainBudget = $(lift (onchainBudget d))
      , onchainLine = $(lift (onchainLine d))
      , onchainResolvedArgs = $(pure (TH.ListE args))
      }
    |]

{-| Resolve one argument's type name to a blueprint definition id.

This is where argument schemas are decided, rather than in
'PlutusTx.Ual.Resolve.attachUal': only the splice has the *type*, and only the
type gives the id. -}
resolvedArgExp :: UalArgument -> TH.Q TH.Exp
resolvedArgExp a = do
  ty <- typeOfName (argTypeName a)
  [|
    ResolvedArgument
      { resolvedEncoding = $(lift (argEncoding a))
      , resolvedDefinitionId = definitionId @($(pure ty))
      }
    |]

{-| Turn an argument type as *written in the annotation* into a TH type.

Handles a plain name (@Ticket@) and a list of one (@[TxInInfo]@) — the two forms
UAL's own examples use. Anything more structured (tuples, applied type
constructors, @Map k v@) is rejected with a clear message rather than guessed at:
there is no TH parser for type syntax, so each form has to be built by hand, and
silently mis-resolving a type would produce a blueprint @$ref@ to the wrong
definition. -}
typeOfName :: Text.Text -> TH.Q TH.Type
typeOfName raw = case Text.stripPrefix "[" t >>= Text.stripSuffix "]" of
  Just inner -> TH.AppT TH.ListT <$> typeOfName (Text.strip inner)
  Nothing
    | Text.any (`elem` (" (),[]" :: String)) t ->
        die
          ( UnresolvedOnchainName
              t
              "only a plain type name or a list of one is supported in an ONCHAIN signature"
          )
    | otherwise ->
        TH.lookupTypeName (Text.unpack t) >>= \case
          Nothing -> die (UnresolvedOnchainName t "no such type is in scope at the splice")
          Just n -> pure (TH.ConT n)
  where
    t = Text.strip raw

{-| Spec §8.2 checks 1 and 2: the @ONCHAIN@ name exists, and the arity it
declares matches the arity of the Haskell binding. -}
checkOnchain :: OnchainDecl -> TH.Q ()
checkOnchain d = do
  let nameText = onchainName d
  TH.lookupValueName (Text.unpack nameText) >>= \case
    Nothing -> die (UnresolvedOnchainName nameText "no such value is in scope at the splice")
    Just n -> do
      actual <- arityOf n
      let declared = length (onchainArgs d)
      if actual /= declared
        then die (ArityMismatch nameText declared actual)
        else pure ()

-- | The number of arrows in a top-level binding's type.
arityOf :: TH.Name -> TH.Q Int
arityOf n =
  TH.reify n >>= \case
    TH.VarI _ ty _ -> pure (countArrows ty)
    other ->
      die
        ( UnresolvedOnchainName
            (Text.pack (TH.nameBase n))
            (Text.pack ("expected a value binding; reify gave " <> show other))
        )
  where
    countArrows = \case
      TH.ForallT _ _ t -> countArrows t
      TH.AppT (TH.AppT TH.ArrowT _) t -> 1 + countArrows t
      _ -> 0

{-| Spec §8.2 check 6: a @UPLC_DATA@ type must be in scope. Whether it has a
@HasBlueprintDefinition@ instance is checked by the caller's use of
@deriveDefinitions@, which is a type error if it does not — so this only needs to
catch a name that does not resolve at all. -}
checkUplcData :: Text.Text -> TH.Q ()
checkUplcData tyText =
  TH.lookupTypeName (Text.unpack tyText) >>= \case
    Nothing -> die (UnresolvedOnchainName tyText "no such type is in scope at the splice")
    Just _ -> pure ()

die :: UalError -> TH.Q a
die = fail . Text.unpack . renderUalError
```

`definitionId` is a `HasBlueprintDefinition` class method re-exported by
`PlutusTx.Blueprint.Definition`, so the import is
`import PlutusTx.Blueprint.Definition (definitionId)` — not the `.Unroll`
submodule.

Create `plutus-tx/src/PlutusTx/Ual.hs`:

```haskell
module PlutusTx.Ual (module X) where

import PlutusTx.Ual.Error as X
import PlutusTx.Ual.Parser as X
import PlutusTx.Ual.Resolve as X
import PlutusTx.Ual.Syntax as X
```

`PlutusTx.Ual.TH` is deliberately **not** re-exported: importing it forces
`TemplateHaskell` on the importer, and only modules that actually carry
annotations need it.

Add `PlutusTx.Ual` and `PlutusTx.Ual.TH` to `exposed-modules`, and
`template-haskell` to the library's `build-depends` if `-Wunused-packages` reports
it missing.

- [ ] **Step 4: Run to verify pass**

Run: `cabal run plutus-tx:plutus-tx-test -- -p '/TH/'`
Expected: PASS, 8 tests.

If the build fails with a GHC stage restriction on `fixtureUal` or
`fixtureContract`, a splice is above a binding it needs — move it down.

If `definitionId @($(pure ty))` fails to parse, the nested splice inside a type
application needs building differently; replace that line with
`resolvedDefinitionId = $(TH.appTypeE [|definitionId|] (pure ty))` and drop the
`TypeApplications` use from the quote.

- [ ] **Step 5: Add negative-case documentation**

The three compile-time failures — unresolvable `ONCHAIN` name, arity mismatch,
unresolvable `UPLC_DATA` type — cannot be unit-tested, because a failing splice
fails the build rather than returning a value. Record them as a manual check
instead. Append to `plutus-tx/test/Ual/Fixture.hs`:

```haskell
{- Manual negative checks. Each of these, pasted into this module above the
`fixtureUal` splice, must fail the build with the quoted message:

  {-@ ONCHAIN nosuch :: Integer -> () @-}
    -> ONCHAIN 'nosuch': no such value is in scope at the splice

  {-@ ONCHAIN ticketSpend :: Integer -> () @-}
    -> ONCHAIN 'ticketSpend': signature declares 1 argument(s)
       but the Haskell type has 2

  {-@ UPLC_DATA NoSuchType @-}
    -> ONCHAIN 'NoSuchType': no such type is in scope at the splice

  {-@ ONCHAIN ticketSpend :: { (Ticket, Integer) : asData } -> Integer -> () @-}
    -> ONCHAIN '(Ticket, Integer)': only a plain type name or a list of one is
       supported in an ONCHAIN signature

Re-run these by hand when changing `PlutusTx.Ual.TH`. A should-not-compile test
harness would be better; there is none in this package today. -}
```

- [ ] **Step 6: Verify recompilation tracking by hand**

Run:
```bash
cabal build plutus-tx:plutus-tx-test
printf '\n-- touched\n' >> plutus-tx/test/Ual/Fixture.hs
cabal build plutus-tx:plutus-tx-test 2>&1 | grep -c "Compiling Ual.Fixture"
git checkout plutus-tx/test/Ual/Fixture.hs
```
Expected: `grep -c` prints `1` — `addDependentFile` forced the rebuild. Appending
a comment rather than an annotation keeps the tests passing either way, so a `0`
here means the mechanism is genuinely not working.

- [ ] **Step 7: Commit**

```bash
git add plutus-tx
git commit --no-verify -m "feat(plutus-tx): ualModule TH splice reads and resolves a module's UAL"
```

---

### Task 9: End-to-end example

**Files:**
- Create: `doc/docusaurus/static/code/Example/Ual/Blueprint/Main.hs`
- Create: `plutus-tx/test/Ual/Golden/end-to-end-plutus.golden.json`
- Create: `plutus-tx/test/Ual/Golden/end-to-end-assurance.golden.json`
- Modify: `plutus-tx/test/Ual/Assurance/Spec.hs`

This task produces the artifact a reader can copy: one module carrying both the
contract and its UAL, and a `main` that writes both documents in the order the
CIP's hash constraint requires.

- [ ] **Step 1: Write the failing end-to-end test**

Add to `plutus-tx/test/Ual/Assurance/Spec.hs` a group that runs the whole
pipeline over `Ual.Fixture` and goldens both outputs. Extend the imports with
`PlutusTx.Ual.Resolve (attachUal)`, `PlutusTx.Blueprint.Write (encodeBlueprint)`,
and `Ual.Fixture (fixtureContract, fixtureUal)` — both were defined in Task 8.

```haskell
endToEndTests :: TestTree
endToEndTests =
  testGroup
    "end to end"
    [ goldenVsText
        "blueprint"
        "test/Ual/Golden/end-to-end-plutus.golden.json"
        (render (either (error . show) encodeBlueprint (attachUal [fixtureUal] fixtureContract)))
    , goldenVsText
        "assurance"
        "test/Ual/Golden/end-to-end-assurance.golden.json"
        ( render
            ( either
                (error . show)
                encodeAssurance
                (buildAssurance pre ref "ticketSpend" [fixtureUal])
            )
        )
    ]
  where
    render = Text.decodeUtf8 . LBS.toStrict
    pre = assurancePreamble doc
    ref = assuranceBlueprint doc
```

`fixtureContract` already carries `validatorId = Just $(ualIdFor 'ticketSpend)`
and `preamblePlutusVersion = PlutusV3`, matching the fixture's
`[version: PlutusV3]`, so `attachUal` finds its validator and the version check
passes.

Add `endToEndTests` to the module's `tests` list.

- [ ] **Step 2: Run and inspect both golden files**

Run: `cabal test plutus-tx:plutus-tx-test`
Expected: PASS, both golden files created.

Check `end-to-end-plutus.golden.json`: the validator carries `id: "ticketSpend"`,
`arguments` with two entries whose `schema` are `$ref`s to `Ticket` and
`Integer`, and `budget` with `exCPU: 1883313`.

Check `end-to-end-assurance.golden.json`: one `formalFragments` entry with id
`Ual.Fixture`, one property `ticket_ok` whose `statement.text` is the fixture's
sentence, `statement.formal.uses` is `["Ual.Fixture"]`, and no `evidence` key.

- [ ] **Step 3: Validate the assurance output against the CIP meta-schema**

The document must validate against the schema in the CIPs checkout. Run:

```bash
check-jsonschema \
  --schemafile /Users/romainsoulat/Documents/GitHub/CIPs/CIP-XXXX/schemas/assurance.json \
  plutus-tx/test/Ual/Golden/end-to-end-assurance.golden.json
```

Expected: `ok -- validation done`.

If `check-jsonschema` is not installed, use `pipx run check-jsonschema …` or any
draft-2020-12 validator. The schema sets no `additionalProperties: false`, so the
`formalFragments` and `uses` extensions validate as-is; a failure means a
*required* field is missing or malformed, most likely `preamble.created` not
matching `^\d{4}-\d{2}-\d{2}$`.

- [ ] **Step 4: Write the documentation example**

Create `doc/docusaurus/static/code/Example/Ual/Blueprint/Main.hs`, modelled on
`doc/docusaurus/static/code/Example/Cip57/Blueprint/Main.hs`. It must contain:
the same pragma block as the Cip57 example (it needs the plugin), a `Ticket`
type with `HasBlueprintDefinition`, an `ONCHAIN`-annotated validator, one
`PREDICATE` block, one `PROPERTY` block, `contractUal = $(ualModule)` as the last
declaration, and:

```haskell
main :: IO ()
main = do
  bp <- either (fail . show) pure (attachUal [contractUal] myContractBlueprint)
  writeBlueprint "plutus.json" bp
  ref <- blueprintRef "plutus.json" "plutus.json"
  doc <-
    either
      (fail . show)
      pure
      (buildAssurance myAssurancePreamble ref "ticketSpend" [contractUal])
  writeAssurance "assurance.json" doc
```

The two-argument `blueprintRef uri path` takes the URI to record in the document
and the path to hash; they coincide here.

Check whether this new example needs registering. Run:
`grep -rn "Cip57" doc/docusaurus/*.cabal doc/docusaurus/**/*.cabal 2>/dev/null | head`
and follow whatever pattern the Cip57 example uses (a `data-files` entry or an
`other-modules` entry in the docusaurus examples stanza).

- [ ] **Step 5: Full test run**

Run: `cabal test plutus-tx:plutus-tx-test && cabal build all 2>&1 | tail -5`
Expected: all tests pass; `cabal build all` reports no errors.

- [ ] **Step 6: Commit**

```bash
git add plutus-tx doc/docusaurus
git commit --no-verify -m "feat(plutus-tx): end-to-end UAL example and golden documents"
```

---

### Task 10: Linear-vesting acceptance exercise

**Files:**
- Create: `docs/superpowers/ual-linear-vesting-acceptance.md`

This is the check spec §10 calls "the acceptance test that matters": does the
document pair actually carry everything the hand-written Lean proofs need? It is
a paper exercise in this slice, because nothing here generates Lean — but doing
it now is what stops slice 2 discovering a missing field after the format is
published.

The reference is `/Users/romainsoulat/contracts-library/formal/Formal/Vesting/Linear/`:
`Script.lean`, `Spec.lean`, `Soundness.lean`, `Completeness.lean`, `Robustness.lean`.

- [ ] **Step 1: Read the five Lean modules and list what they consume**

Run:
```bash
ls /Users/romainsoulat/contracts-library/formal/Formal/Vesting/Linear/
cat /Users/romainsoulat/contracts-library/formal/Formal/Vesting/Linear/Script.lean
cat /Users/romainsoulat/contracts-library/formal/Formal/Common.lean
```

For each Lean module, write down every input it needs that is *not* Lean source
it already contains. Expect at least: the compiled validator (from
`#import_blueprints` over `compiledCode`), the datum/redeemer types (from
`definitions`), the applied-argument list and its encodings, and an execution
bound (`validatorAccepts` passes `2500` — a *step* count, not `exCPU`).

- [ ] **Step 2: Hand-write the document pair for linear vesting**

In the acceptance document, write out (as JSON, inline) the `validators` entry
this design would emit for `linear_vesting.spend`, and the `formalFragments` plus
`properties` entries for the theorems `Soundness.lean` and `Robustness.lean`
state. Take the theorem names and statements from the Lean files; take the
natural-language text from `Formal/Vesting/Linear/README.md`, which already has a
sentence per theorem in its tables.

- [ ] **Step 3: Record every gap you find**

For each Lean input from Step 1 that the document pair cannot supply, write: what
is missing, whether it belongs in the blueprint or the assurance document, and
whether it blocks slice 2. Two are known already and must appear in the list:

- **`exCPU`/`exMem` versus a step bound.** `validatorAccepts` takes a step count;
  UAL declares cost-model units. Nothing in this slice converts between them.
- **Per-property scope.** Every property this slice emits is scoped to a single
  validator id passed to `buildAssurance`. `Soundness.lean` and `Robustness.lean`
  are all about the same validator, so linear vesting does not expose this — but a
  multi-validator contract would, and UAL's `PROPERTY` syntax has no scope field.

- [ ] **Step 4: Commit**

```bash
git add docs/superpowers/ual-linear-vesting-acceptance.md
git commit --no-verify -m "docs: linear-vesting acceptance check for the UAL document pair"
```

---

### Task 11: CIP revisions

**Files:**
- Modify: `/Users/romainsoulat/Documents/GitHub/CIPs/CIP-XXXX/README.md`
- Modify: `/Users/romainsoulat/Documents/GitHub/CIPs/CIP-XXXX/schemas/assurance.json`
- Create: `/Users/romainsoulat/Documents/GitHub/CIPs/CIP-XXXX/examples/assurance-ual-generated.json`

This is a different git repository, on branch `cip/extended-blueprints-verification`.
Commit there separately. The six revisions are spec §8.3.

- [ ] **Step 1: Confirm the branch**

Run: `git -C /Users/romainsoulat/Documents/GitHub/CIPs branch --show-current`
Expected: `cip/extended-blueprints-verification`.

- [ ] **Step 2: Rewrite Rationale reason #2**

In `CIP-XXXX/README.md`, under "Why a detached document rather than a blueprint
extension", replace item 2 with text that distinguishes hand-maintained from
generated content. The current text is:

> 2. **Blueprints are compiler output.** `plutus.json` is typically regenerated on every build by the smart-contract framework (Aiken, OpShin, plu-ts, ...). Hand-maintained assurance data embedded in a generated file would be overwritten on each compilation, or would require every framework to learn how to preserve and merge it.

Replace with:

> 2. **Hand-maintained data does not survive a generated file.** `plutus.json` is regenerated on every build by the smart-contract framework (Aiken, OpShin, plu-ts, ...). Assurance data maintained by hand inside it would be overwritten on each compilation, or would require every framework to learn how to preserve and merge it. This argument does *not* apply to assurance content derived from source annotations, which a toolchain can regenerate as freely as the blueprint itself — see [Producers](#producers). It is the first and third reasons above that make detachment right in both cases.

- [ ] **Step 3: Add the Producers subsection**

After "Consumer obligations", add a `#### Producers` subsection stating: output
MUST be deterministic for a given source tree so that regeneration produces no
spurious diff; `preamble.authors` and `preamble.created` SHOULD come from project
metadata rather than the wall clock, so that rebuilding an old commit reproduces
its document; and `blueprint.hash` MUST be computed over the blueprint document
as finally written, which constrains build order — write `plutus.json` first,
hash it, then write the assurance document.

- [ ] **Step 4: Add `formalFragments` and `uses` to the spec text**

Add a `#### formalFragments` subsection after "Statements", documenting the
optional top-level field as a list of objects with `id` (unique, matching
`^[A-Za-z0-9_.-]+$`), `language` (a `languages` key), optional `imports` (ids of
other fragments), and `source`. State the consumer obligation: fragments are
opaque text in the named language; a consumer that does not know the language
MUST ignore them rather than reject the document. Extend the Statements table
with the optional `uses` field on `formal`: a list of fragment ids the formal
statement elaborates against.

Then add both to `schemas/assurance.json`: a `formalFragments` property on the
root object referencing a new `$defs/formalFragment`, and a `uses` property
inside `$defs/statement`'s `formal` object. Adding them to the schema is
declarative only — the schema has no `additionalProperties: false`, so documents
already validate; declaring them gives consumers something to check against.

Note the `id` pattern must permit `.` — fragment ids are module names like
`My.Contract` — which is *wider* than the property-`id` pattern
`^[A-Za-z0-9_-]+$`. Do not reuse that pattern.

- [ ] **Step 5: Widen "Validators only"**

Replace the "Validators only" rationale subsection so it covers `ONCHAIN`
functions: a producer MAY emit a `validators` entry for any named compiled
program with argument schemas, not only a script the ledger invokes directly,
since that is mechanically what a CIP-0057 validator entry describes. Keep the
existing sentence that finer-grained per-function contracts *within* a validator
remain out of scope.

- [ ] **Step 6: Note the blueprint companion fields**

In "Why the specification language is free", add a sentence: a `formal.language`
implementation MAY require additional fields in the blueprint itself (for
instance an ordered applied-argument list with encoding schemes, and an execution
budget). Such fields are legal CIP-0057 additions — validator objects do not
forbid additional fields — and are specified by that language, not by this CIP.

- [ ] **Step 7: Promote validator `id`**

In "Referencing validators", after the RECOMMENDED sentence, note that producers
generating assurance documents from source annotations emit `id` for every
validator they describe, since the id is what binds an annotation to a validator.

- [ ] **Step 8: Add the generated example**

Copy the end-to-end output as a CIP example:

```bash
cp plutus-tx/test/Ual/Golden/end-to-end-assurance.golden.json \
   /Users/romainsoulat/Documents/GitHub/CIPs/CIP-XXXX/examples/assurance-ual-generated.json
```

Add a `<details>` block for it in the README's Examples section, titled
"Compiler-generated from source annotations (formalFragments, no evidence)", with
a sentence noting that its properties carry no evidence records because it is
emitted at build time, before any proof — the "stated, unverified claim" case.

Then validate every example against the schema:

```bash
cd /Users/romainsoulat/Documents/GitHub/CIPs
for f in CIP-XXXX/examples/*.json; do
  check-jsonschema --schemafile CIP-XXXX/schemas/assurance.json "$f"
done
```
Expected: `ok -- validation done` for each.

- [ ] **Step 9: Commit in the CIPs repo**

```bash
git -C /Users/romainsoulat/Documents/GitHub/CIPs add CIP-XXXX
git -C /Users/romainsoulat/Documents/GitHub/CIPs commit -m "CIP-XXXX: compiler-generated assurance documents and formal fragments"
```

---

### Task 12: UAL doc corrections

**Files:**
- Create: `docs/superpowers/ual-doc-corrections.md`

The UAL specification is a Google Doc, which cannot be edited from here. Produce
a reviewable list to hand to its authors.

- [ ] **Step 1: Write the corrections document**

Create `docs/superpowers/ual-doc-corrections.md` containing the seven items of
spec §9, each with: the section of the UAL doc, what it currently says, what it
should say, and the evidence. The delimiter item must include the reproduction:

```
$ printf 'module D1 where\n{-@ ONCHAIN foo -@}\nfoo :: Int\nfoo = 1\n' > D1.hs
$ ghc -fno-code D1.hs
D1.hs:2:1: error: [GHC-21231] unterminated `{-' at end of input
```

State for each item whether this implementation already follows the corrected
form (delimiter, import direction, `PROPERTY` text field, positional arguments —
yes; `#prep_uplc`, `PlutusV4`, `IsScott` — deferred to a later slice).

- [ ] **Step 2: Correct our own spec**

Two claims in `docs/superpowers/specs/2026-08-24-ual-extended-blueprints-design.md`
turned out to be wrong while planning, and the spec is the document slice 2 will
be planned from. Fix both:

- **§7's component table** lists "`compile`-splice generation for `ONCHAIN`
  functions" under `PlutusTx.Ual.TH`. Remove it and note why: the splice needs the
  `plinthc` marker from `plutus-tx-plugin`, which `plutus-tx` cannot depend on. Add
  a sentence to **§4.4** saying the author writes the `compile` call and sets
  `validatorCompiled` by hand, and that a helper would have to live in
  `plutus-tx-plugin` if it is ever wanted.
- **§8.2 check 6** says a `UPLC_DATA` type is checked for a
  `HasBlueprintDefinition` instance. The splice only checks the *name resolves*;
  the instance is enforced by the author's `deriveDefinitions @[…]`, which is a
  type error without it. Reword the check to match what is actually enforced, and
  say where the real enforcement lives.

- [ ] **Step 3: Commit**

```bash
git add docs/superpowers
git commit --no-verify -m "docs: UAL spec corrections and the list to hand back upstream"
```

---

## Notes on things that will bite

**`ContractBlueprint` is existential.** You cannot pattern-match a validator out
of it and keep its `referencedTypes` index. Any test that inspects a validator
must go through `Aeson.toJSON`. This is why Task 5's tests are written against
`Aeson.Value` rather than the record.

**`Set (ValidatorBlueprint …)` ordering.** `contractValidators` is a `Set`, so
`Set.toList` order follows the derived `Ord`, which starts at `validatorTitle`.
Tests that index into the validators array must either use one validator or give
the validators titles whose order you have checked.

**`Set.map` needs `Ord`.** `attachUal` uses `Set.map fill`, which requires
`Ord (ValidatorBlueprint referencedTypes)`. It is already derived. But note
`Set.map` collapses duplicates: if `fill` maps two distinct validators to equal
values, one is silently dropped. It cannot happen here — `fill` never changes
`validatorTitle`, which distinguishes them — but do not generalise it.

**`-Wunused-packages` is unforgiving.** After each task, if the build complains
about an unused package you added, remove it. If it complains about one you did
*not* add, you have removed the last use of an existing import — check your edit.

**Golden files are created, not diffed, on first run.** A brand-new golden test
always "passes". Read the file before committing it; a wrong golden that was
never inspected is worse than no test.
