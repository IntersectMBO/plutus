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
