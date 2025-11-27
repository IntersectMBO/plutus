{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}

module PlutusCore.Arity where

import Data.Proxy
import PlutusCore
import PlutusCore.Builtin
import Prettyprinter

-- | Is the next argument a term or a type?
data Param
  = TermParam
  | TypeParam
  deriving stock (Show, Eq)

instance Pretty Param where
  pretty = viaShow

{-|
The (syntactic) arity of a term. That is, a record of the arguments that the
term expects before it may do some work. Since we have both type and lambda
abstractions, this is not a simple argument count, but rather a list of values
indicating whether the next argument should be a term or a type.

Note that this is the syntactic arity, i.e. it just corresponds to the number of
syntactic lambda and type abstractions on the outside of the term. It is thus
an under-approximation of how many arguments the term may need.
e.g. consider the term @let id = \x -> x in id@: the variable @id@ has syntactic
arity @[]@, but does in fact need an argument before it does any work. -}
type Arity = [Param]

-- | Get the 'Arity' from a 'TypeScheme'.
typeSchemeArity :: TypeScheme val args res -> Arity
typeSchemeArity TypeSchemeResult {} = []
typeSchemeArity (TypeSchemeArrow sch) = TermParam : typeSchemeArity sch
typeSchemeArity (TypeSchemeAll _ sch) = TypeParam : typeSchemeArity sch

-- | Get the arity of a builtin function from the 'PLC.BuiltinSemanticsVariant'.
builtinArity
  :: forall uni fun
   . ToBuiltinMeaning uni fun
  => Proxy uni
  -> BuiltinSemanticsVariant fun
  -> fun
  -> Arity
builtinArity _ semvar fun =
  case toBuiltinMeaning @uni @fun @(Term TyName Name uni fun ()) semvar fun of
    BuiltinMeaning sch _ _ -> typeSchemeArity sch
