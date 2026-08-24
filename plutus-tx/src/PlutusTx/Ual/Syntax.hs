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

{-| Which kind of UAL block this is. The @K@ prefix is load-bearing: 'UalBlock'
lives in this module too and has the same four variants, so the bare names
would clash. -}
data BlockKind = KOnchain | KPredicate | KProperty | KUplcData
  deriving stock (Eq, Ord, Show)

{-| A @{-\@@ … @\@-}@ block exactly as the lexer found it: the kind keyword, and
everything after it, untouched. -}
data RawBlock = MkRawBlock
  { rawKind :: BlockKind
  , rawBody :: Text
  -- ^ Everything after the kind keyword, verbatim, with no trimming.
  , rawLine :: Int
  -- ^ 1-based line of the opening @{-\@@.
  }
  deriving stock (Eq, Show)

data LexedModule = MkLexedModule
  { lexedModuleName :: Maybe UalModuleName
  , lexedImports :: [UalModuleName]
  , lexedBlocks :: [RawBlock]
  }
  deriving stock (Eq, Show)

{-| One argument of an @ONCHAIN@ refined signature, as written. Positional: UAL
gives types, not names. -}
data UalArgument = MkUalArgument
  { argTypeName :: Text
  -- ^ Source text of the type, e.g. @"CurrencySymbol"@.
  , argEncoding :: ArgumentEncoding
  }
  deriving stock (Eq, Show, Lift)

{-| A 'UalArgument' whose type name has been resolved to a blueprint definition
id. Produced only by the Template Haskell splice, which is the only place that
has the Haskell type to hand.

No 'Lift' instance, deliberately: 'DefinitionId' does not export its
constructor, so a stock-derived instance would splice a name that is out of
scope at the use site. Callers that need to lift this build it field by
field. -}
data ResolvedArgument = MkResolvedArgument
  { resolvedEncoding :: ArgumentEncoding
  , resolvedDefinitionId :: DefinitionId
  }
  deriving stock (Eq, Show)

data OnchainDecl = MkOnchainDecl
  { onchainName :: Text
  , onchainArgs :: [UalArgument]
  , onchainResult :: Text
  -- ^ Source text of the result type.
  , onchainVersion :: Maybe PlutusVersion
  , onchainBudget :: Maybe ExecutionBudget
  , onchainLine :: Int
  , onchainResolvedArgs :: [ResolvedArgument]
  -- ^ Empty as the parser produces it; the Template Haskell splice fills it in.
  }
  deriving stock (Eq, Show)

data PropertyDecl = MkPropertyDecl
  { propertyName :: Text
  , propertyText :: Text
  -- ^ The natural-language statement.
  , propertyBody :: Text
  -- ^ The formal statement, verbatim.
  , propertyLine :: Int
  }
  deriving stock (Eq, Show, Lift)

{-| A parsed UAL block. The @B@ prefix is load-bearing: 'BlockKind' lives in
this module too and has the same four variants, so the bare names would
clash. -}
data UalBlock
  = BOnchain OnchainDecl
  | BPredicate Text
  -- ^ The body, verbatim.
  | BProperty PropertyDecl
  | BUplcData Text
  -- ^ The type name.
  deriving stock (Eq, Show)

-- | Everything one surface module contributes.
data ModuleUal = MkModuleUal
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
emptyModuleUal n = MkModuleUal n [] [] [] [] []
