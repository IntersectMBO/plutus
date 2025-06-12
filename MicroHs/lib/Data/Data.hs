module Data.Data(Data(..), module Data.Typeable) where
import Data.Typeable

-- Fake Data class until the type checker bug has been fixed
class (Typeable a) => Data a
