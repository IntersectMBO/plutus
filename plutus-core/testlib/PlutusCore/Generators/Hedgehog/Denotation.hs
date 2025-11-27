{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

{-| This module defines tools for associating PLC terms with their corresponding
Haskell values. -}
module PlutusCore.Generators.Hedgehog.Denotation
  ( KnownType
  , Denotation (..)
  , DenotationContextMember (..)
  , DenotationContext (..)
  , lookupInContext
  , denoteVariable
  , insertVariable
  , insertBuiltin
  , typedBuiltins
  ) where

import PlutusCore.Builtin
import PlutusCore.Core
import PlutusCore.Default
import PlutusCore.Name.Unique
import PlutusPrelude

import Data.Dependent.Map (DMap)
import Data.Dependent.Map qualified as DMap
import Data.Functor.Compose
import Type.Reflection

type KnownType val a = (KnownTypeAst TyName (UniOf val) a, MakeKnown val a)

-- | Haskell denotation of a PLC object. An object can be a 'Builtin' or a variable for example.
data Denotation term object res = forall args. Denotation
  { _denotationObject :: object
  -- ^ A PLC object.
  , _denotationToTerm :: object -> term
  -- ^ How to embed the object into a term.
  , _denotationItself :: FoldArgs args res
  -- ^ The denotation of the object. E.g. the denotation of 'AddInteger' is '(+)'.
  , _denotationScheme :: TypeScheme term args res
  -- ^ The 'TypeScheme' of the object.
  }

{-| A member of a 'DenotationContext'.
@object@ is existentially quantified, so the only thing that can be done with it,
is turning it into a 'Term' using '_denotationToTerm'. -}
data DenotationContextMember term res
  = forall object. DenotationContextMember (Denotation term object res)

{-| A context of 'DenotationContextMember's.
Each row is a mapping from a type to a list of things that can return that type.
For example it can contain a mapping from @integer@ to
  1. a bound variable of type @integer@
  2. a bound variable of functional type with the result being @integer@
  3. the 'AddInteger' 'Builtin' or any other 'Builtin' which returns an @integer@. -}
newtype DenotationContext term = DenotationContext
  { unDenotationContext :: DMap TypeRep (Compose [] (DenotationContextMember term))
  }

{-| Look up a list of 'Denotation's from 'DenotationContext' each of which has a type that ends in
the same type as the one that the 'TypeRep' argument represents. -}
lookupInContext
  :: forall a term
   . TypeRep a
  -> DenotationContext term
  -> [DenotationContextMember term a]
lookupInContext tr = foldMap getCompose . DMap.lookup tr . unDenotationContext

-- Here the only search that we need to perform is the search for things that return an appropriate
-- @r@, be them variables or functions. Better if we also take types of arguments into account,
-- but it is not required as we can always generate an argument out of thin air in a rank-0 setting
-- (without @Void@).

-- | The resulting type of a 'TypeScheme'.
withTypeSchemeResult :: TypeScheme term args res -> (KnownType term res => TypeRep res -> c) -> c
withTypeSchemeResult TypeSchemeResult k = k typeRep
withTypeSchemeResult (TypeSchemeArrow schB) k = withTypeSchemeResult schB k
withTypeSchemeResult (TypeSchemeAll _ schK) k = withTypeSchemeResult schK k

-- | Get the 'Denotation' of a variable.
denoteVariable
  :: KnownType (Term TyName Name uni fun ()) res
  => Name -> TypeRep res -> res -> Denotation (Term TyName Name uni fun ()) Name res
denoteVariable name tr meta = withTypeable tr $ Denotation name (Var ()) meta TypeSchemeResult

-- | Insert the 'Denotation' of an object into a 'DenotationContext'.
insertDenotation
  :: TypeRep res -> Denotation term object res -> DenotationContext term -> DenotationContext term
insertDenotation tr denotation (DenotationContext vs) =
  DenotationContext $
    DMap.insertWith'
      (\(Compose xs) (Compose ys) -> Compose $ xs ++ ys)
      tr
      (Compose [DenotationContextMember denotation])
      vs

-- | Insert a variable into a 'DenotationContext'.
insertVariable
  :: KnownType (Term TyName Name uni fun ()) a
  => Name
  -> TypeRep a
  -> a
  -> DenotationContext (Term TyName Name uni fun ())
  -> DenotationContext (Term TyName Name uni fun ())
insertVariable name tr = insertDenotation tr . denoteVariable name tr

-- | Insert a builtin into a 'DenotationContext'.
insertBuiltin
  :: DefaultFun
  -> DenotationContext (Term TyName Name DefaultUni DefaultFun ())
  -> DenotationContext (Term TyName Name DefaultUni DefaultFun ())
insertBuiltin fun =
  case toBuiltinMeaning def fun of
    BuiltinMeaning sch meta _ ->
      withTypeSchemeResult sch $ \tr ->
        insertDenotation tr $ Denotation fun (Builtin ()) meta sch

{-| A 'DenotationContext' that consists of 'DefaultFun's.

DEPRECATED: No need to update for a new builtin.
Outdated, since we moved to quickcheck generators. -}
typedBuiltins
  :: DenotationContext (Term TyName Name DefaultUni DefaultFun ())
typedBuiltins =
  insertBuiltin AddInteger
    . insertBuiltin SubtractInteger
    . insertBuiltin MultiplyInteger
    -- We insert those, but they don't really get selected, because the 'TypeRep' of
    -- @EvaluationResult Integer@ is different to the one of @Integer@ and when selection is
    -- performed only the latter is considered. Maybe we should add @EvaluationResult Integer@ to
    -- the set of built-in types to pick up from. Or maybe we should stop using 'TypeRep' and use
    -- something custom. Or maybe we should just remove these tests altogether.
    . insertBuiltin DivideInteger
    . insertBuiltin RemainderInteger
    . insertBuiltin QuotientInteger
    . insertBuiltin ModInteger
    . insertBuiltin LessThanInteger
    . insertBuiltin LessThanEqualsInteger
    . insertBuiltin EqualsInteger
    . insertBuiltin AppendByteString
    . insertBuiltin Sha2_256
    . insertBuiltin Sha3_256
    . insertBuiltin Blake2b_224
    . insertBuiltin Blake2b_256
    . insertBuiltin Keccak_256
    . insertBuiltin Ripemd_160
    . insertBuiltin EqualsByteString
    $ DenotationContext mempty
