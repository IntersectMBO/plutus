module Text.Pretty
  ( class Pretty
  , pretty
  , Doc
  , class Args
  , hasArgs
  , hasNestedArgs
  , text
  , class GenericArgs
  , gHasArgs
  , gHasNestedArgs
  , genericHasArgs
  , genericHasNestedArgs
  , genericPretty
  ) where

import Prelude
import Data.BigInteger (BigInteger)
import Data.Foldable (any, intercalate)
import Data.Generic.Rep (class Generic, Argument(..), Constructor(..), NoArguments, Product(..), Sum(..), from)
import Data.String.Extra (repeat)
import Data.Symbol (class IsSymbol, SProxy(..), reflectSymbol)

data Doc
  = Text String
  | Newline Int
  | Cat Doc Doc
  | Empty

instance showDoc :: Show Doc where
  show Empty = mempty
  show (Text str) = str
  show (Newline n) = "\n" <> repeat n " "
  show (Cat a b) = show a <> show b

instance semigroupDoc :: Semigroup Doc where
  append = Cat

instance monoidDoc :: Monoid Doc where
  mempty = Empty

newline :: Doc
newline = Newline 0

catNewline :: Doc -> Doc -> Doc
catNewline a b = a <> newline <> b

infixr 5 catNewline as </>

text :: String -> Doc
text = Text

indent :: Int -> Doc -> Doc
indent n (Newline m) = Newline (m + n)

indent n (Cat a b) = Cat (indent n a) (indent n b)

indent _ doc = doc

------------------------ Pretty Class and Generic Instances ---------------------------
class Pretty a where
  pretty :: a -> Doc

instance prettyString :: Pretty String where
  pretty = text <<< show

instance prettyBigInteger :: Pretty BigInteger where
  pretty = text <<< show

instance prettyNoArguments :: Pretty NoArguments where
  pretty _ = mempty

instance prettyArray :: Pretty a => Pretty (Array a) where
  pretty xs =
    let
      docs = map pretty xs

      list = intercalate (text ", ") docs
    in
      text "[" <> list <> text "]"

instance prettySum :: (Pretty l, Pretty r) => Pretty (Sum l r) where
  pretty (Inl l) = pretty l
  pretty (Inr r) = pretty r

instance prettyArgument :: (Pretty a, Args a) => Pretty (Argument a) where
  pretty (Argument a) =
    if hasArgs a then
      text "(" <> pretty a <> (if hasNestedArgs a then newline else mempty) <> text ")"
    else
      pretty a

instance prettyProduct :: (GenericArgs l, GenericArgs r, Pretty l, Pretty r) => Pretty (Product l r) where
  pretty (Product l r) = pretty l <> (if (gHasArgs l || gHasArgs r) then newline else text " ") <> pretty r

instance prettyConstructor :: (GenericArgs a, Pretty a, IsSymbol name) => Pretty (Constructor name a) where
  pretty (Constructor a) =
    if gHasNestedArgs a then
      text conName <> indent 4 (newline <> pretty a)
    else
      text conName <> text " " <> pretty a
    where
    conName :: String
    conName = reflectSymbol (SProxy :: SProxy name)

genericPretty :: forall a rep. Generic a rep => Pretty rep => a -> Doc
genericPretty x = pretty (from x)

class Args a where
  hasArgs :: a -> Boolean
  hasNestedArgs :: a -> Boolean

instance hasArgsString :: Args String where
  hasArgs _ = false
  hasNestedArgs _ = false

instance hasArgsBigInteger :: Args BigInteger where
  hasArgs _ = false
  hasNestedArgs _ = false

instance argsArray :: Args a => Args (Array a) where
  hasArgs as = false
  hasNestedArgs as = any hasNestedArgs as

class GenericArgs a where
  gHasArgs :: a -> Boolean
  gHasNestedArgs :: a -> Boolean

instance argsSum :: (GenericArgs l, GenericArgs r) => GenericArgs (Sum l r) where
  gHasArgs (Inl l) = gHasArgs l
  gHasArgs (Inr r) = gHasArgs r
  gHasNestedArgs (Inl l) = gHasNestedArgs l
  gHasNestedArgs (Inr r) = gHasNestedArgs r

instance argsNoArguments :: GenericArgs NoArguments where
  gHasArgs _ = false
  gHasNestedArgs _ = false

instance argsArgument :: Args a => GenericArgs (Argument a) where
  gHasArgs (Argument a) = hasArgs a
  gHasNestedArgs (Argument a) = hasNestedArgs a

instance argsGeneric1 :: Args a => GenericArgs (Constructor name (Argument a)) where
  gHasArgs (Constructor (Argument a)) = true
  gHasNestedArgs (Constructor (Argument a)) = false

instance argsGeneric2 :: GenericArgs (Constructor name NoArguments) where
  gHasArgs (Constructor a) = false
  gHasNestedArgs (Constructor a) = false

instance argsProdcutArgs :: (Args a, Args b) => GenericArgs (Product (Argument a) (Argument b)) where
  gHasArgs (Product (Argument l) (Argument r)) = true
  gHasNestedArgs (Product (Argument l) (Argument r)) = hasArgs l || hasArgs r
else instance argsProdcut :: (Args a, GenericArgs b) => GenericArgs (Product (Argument a) b) where
  gHasArgs (Product _ _) = true
  gHasNestedArgs (Product (Argument l) r) = hasArgs l || gHasArgs r

instance argsGeneric :: (Args a, Args b) => GenericArgs (Constructor name (Product (Argument a) (Argument b))) where
  gHasArgs (Constructor (Product l r)) = true
  gHasNestedArgs (Constructor (Product (Argument l) (Argument r))) = hasArgs l || hasArgs r
else instance argsGenericProdcutL :: (Args a, GenericArgs b) => GenericArgs (Constructor name (Product (Argument a) b)) where
  gHasArgs (Constructor (Product l r)) = true
  gHasNestedArgs (Constructor (Product (Argument l) r)) = hasArgs l || gHasArgs r

genericHasArgs :: forall a rep. Generic a rep => GenericArgs rep => a -> Boolean
genericHasArgs = gHasArgs <<< from

genericHasNestedArgs :: forall a rep. Generic a rep => GenericArgs rep => a -> Boolean
genericHasNestedArgs = gHasNestedArgs <<< from
