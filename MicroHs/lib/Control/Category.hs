module Control.Category(module Control.Category) where
import qualified Prelude()
import Primitives
import qualified Data.Function as F

infixr 9 .
infixr 1 >>>, <<<

class Category cat where
    id :: cat a a
    (.) :: cat b c -> cat a b -> cat a c

instance Category (->) where
    id = F.id
    (.) = (F..)

(<<<) :: Category cat => cat b c -> cat a b -> cat a c
(<<<) = (.)

(>>>) :: Category cat => cat a b -> cat b c -> cat a c
f >>> g = g . f
