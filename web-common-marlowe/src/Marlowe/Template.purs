module Marlowe.Template where

import Prelude
import Data.BigInteger (BigInteger)
import Data.Lens (Lens')
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Newtype (class Newtype)
import Data.Set (Set)
import Data.Symbol (SProxy(..))
import Data.Traversable (foldMap)

newtype Placeholders
  = Placeholders
  { slotPlaceholderIds :: Set String
  , valuePlaceholderIds :: Set String
  }

derive instance newTypePlaceholders :: Newtype Placeholders _

-- The eq and show instances are required for doing property based testing with quickcheck
-- and are not needed by the actual code.
derive newtype instance eqPlaceholders :: Eq Placeholders

derive newtype instance showPlaceholders :: Show Placeholders

derive newtype instance semigroupPlaceholders :: Semigroup Placeholders

derive newtype instance monoidPlaceholders :: Monoid Placeholders

data IntegerTemplateType
  = SlotContent
  | ValueContent

newtype TemplateContent
  = TemplateContent
  { slotContent :: Map String BigInteger
  , valueContent :: Map String BigInteger
  }

_slotContent :: Lens' TemplateContent (Map String BigInteger)
_slotContent = _Newtype <<< prop (SProxy :: SProxy "slotContent")

_valueContent :: Lens' TemplateContent (Map String BigInteger)
_valueContent = _Newtype <<< prop (SProxy :: SProxy "valueContent")

typeToLens :: IntegerTemplateType -> Lens' TemplateContent (Map String BigInteger)
typeToLens SlotContent = _slotContent

typeToLens ValueContent = _valueContent

derive instance newTypeTemplateContent :: Newtype TemplateContent _

derive newtype instance semigroupTemplateContent :: Semigroup TemplateContent

derive newtype instance monoidTemplateContent :: Monoid TemplateContent

initializeWith :: forall a b. Ord a => (a -> b) -> Set a -> Map a b
initializeWith f = foldMap (\x -> Map.singleton x $ f x)

initializeTemplateContent :: Placeholders -> TemplateContent
initializeTemplateContent ( Placeholders
    { slotPlaceholderIds, valuePlaceholderIds }
) =
  TemplateContent
    { slotContent: initializeWith (const one) slotPlaceholderIds
    , valueContent: initializeWith (const zero) valuePlaceholderIds
    }

updateTemplateContent :: Placeholders -> TemplateContent -> TemplateContent
updateTemplateContent ( Placeholders { slotPlaceholderIds, valuePlaceholderIds }
) (TemplateContent { slotContent, valueContent }) =
  TemplateContent
    { slotContent: initializeWith (\x -> fromMaybe one $ Map.lookup x slotContent) slotPlaceholderIds
    , valueContent: initializeWith (\x -> fromMaybe zero $ Map.lookup x valueContent) valuePlaceholderIds
    }

class Template a b where
  getPlaceholderIds :: a -> b

class Fillable a b where
  fillTemplate :: b -> a -> a
