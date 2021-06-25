module Validation where

import Prelude
import Data.Array (elem, mapWithIndex)
import Data.Array as Array
import Data.Foldable (class Foldable)
import Data.Functor.Foldable (Fix)
import Data.Generic.Rep (class Generic)
import Data.Json.JsonTuple (JsonTuple(..))
import Data.Lens (Lens', view)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Data.Tuple (Tuple(..))
import Matryoshka (Algebra, cata)
import Playground.Types (ContractCall(..), _FunctionSchema)
import Schema (FormArgumentF(..))

isValid :: forall a. Validation a => a -> Boolean
isValid = Array.null <<< validate

class Validation a where
  validate :: a -> Array (WithPath ValidationError)

data ValidationError
  = Required
  | Invalid
  | Unsupported

derive instance eqValidationError :: Eq ValidationError

derive instance genericValidationError :: Generic ValidationError _

instance showValidationError :: Show ValidationError where
  show Required = "Required"
  show Invalid = "Invalid"
  show Unsupported = "Unsupported"

------------------------------------------------------------
newtype WithPath a
  = WithPath { path :: Array String, value :: a }

derive instance eqWithPath :: Eq a => Eq (WithPath a)

derive instance functorWithPath :: Functor WithPath

instance showWithPath :: Show a => Show (WithPath a) where
  show (WithPath { path, value }) = Array.intercalate "." path <> ": " <> show value

showPathValue :: forall a. Show a => WithPath a -> String
showPathValue (WithPath { value }) = show value

noPath :: forall a. a -> WithPath a
noPath value = WithPath { path: [], value }

withPath :: forall a f. Foldable f => f String -> a -> WithPath a
withPath path value = WithPath { path: Array.fromFoldable path, value }

addPath :: forall a. String -> WithPath a -> WithPath a
addPath parent (WithPath { path, value }) = WithPath { path: Array.cons parent path, value }

joinPath :: forall a. Array String -> WithPath a -> WithPath a
joinPath ancestors (WithPath { path, value }) = WithPath { path: ancestors <> path, value }

------------------------------------------------------------
instance formArgumentValidation :: Validation (Fix FormArgumentF) where
  validate = cata algebra
    where
    algebra :: Algebra FormArgumentF (Array (WithPath ValidationError))
    algebra (FormUnitF) = []

    algebra (FormBoolF _) = []

    algebra (FormIntF (Just _)) = []

    algebra (FormIntF Nothing) = [ noPath Required ]

    algebra (FormIntegerF (Just _)) = []

    algebra (FormIntegerF Nothing) = [ noPath Required ]

    algebra (FormStringF (Just _)) = []

    algebra (FormStringF Nothing) = [ noPath Required ]

    algebra (FormHexF (Just _)) = []

    algebra (FormHexF Nothing) = [ noPath Required ]

    algebra (FormRadioF options (Just x)) =
      if x `elem` options then
        []
      else
        [ noPath Invalid ]

    algebra (FormRadioF _ Nothing) = [ noPath Required ]

    algebra (FormTupleF xs ys) =
      Array.concat
        [ addPath "_1" <$> xs
        , addPath "_2" <$> ys
        ]

    algebra (FormMaybeF _ Nothing) = [ noPath Required ]

    algebra (FormMaybeF _ (Just x)) = addPath "_Just" <$> x

    algebra (FormArrayF _ xs) = Array.concat $ mapWithIndex (\i values -> addPath (show i) <$> values) xs

    algebra (FormObjectF xs) = Array.concat $ map (\(JsonTuple (Tuple name values)) -> addPath name <$> values) xs

    algebra (FormValueF x) = []

    algebra (FormPOSIXTimeRangeF _) = []

    algebra (FormUnsupportedF _) = [ noPath Unsupported ]

------------------------------------------------------------
instance simulatorActionValidation :: Validation (ContractCall (Fix FormArgumentF)) where
  validate (AddBlocks _) = []
  validate (AddBlocksUntil _) = []
  validate (PayToWallet _) = []
  validate (CallEndpoint call) = validate arg
    where
    arg :: Fix FormArgumentF
    arg = view (_argumentValues <<< _FunctionSchema <<< _argument) call

_argument :: forall r a. Lens' { argument :: a | r } a
_argument = prop (SProxy :: SProxy "argument")

_argumentValues :: forall r a. Lens' { argumentValues :: a | r } a
_argumentValues = prop (SProxy :: SProxy "argumentValues")
