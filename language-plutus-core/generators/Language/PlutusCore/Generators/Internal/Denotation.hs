-- | This module defines tools for associating PLC terms with their corresponding
-- Haskell values.

{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeOperators             #-}

module Language.PlutusCore.Generators.Internal.Denotation
    ( Denotation(..)
    , DenotationContextMember(..)
    , DenotationContext(..)
    , denoteVariable
    , builtinNameToTerm
    , denoteTypedBuiltinName
    , insertVariable
    , insertTypedBuiltinName
    , typedBuiltinNames
    ) where

import           Language.PlutusCore.Generators.Internal.Dependent

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Core
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Universe

import qualified Data.ByteString.Lazy                              as BSL
import qualified Data.ByteString.Lazy.Hash                         as Hash
import           Data.Coerce
import           Data.Dependent.Map                                (DMap)
import qualified Data.Dependent.Map                                as DMap
import           Data.Functor.Compose
import           Data.Proxy
import           Data.Text                                         (append, pack)
import           GHC.TypeLits

-- | Haskell denotation of a PLC object. An object can be a 'BuiltinName' or a variable for example.
data Denotation uni object res = forall args. Denotation
    { _denotationObject :: object                             -- ^ A PLC object.
    , _denotationToTerm :: object -> Term TyName Name uni ()  -- ^ How to embed the object into a term.
    , _denotationItself :: FoldArgs args res                  -- ^ The denotation of the object.
                                                              -- E.g. the denotation of 'AddInteger' is '(+)'.
    , _denotationScheme :: TypeScheme uni args res            -- ^ The 'TypeScheme' of the object.
    }

-- | A member of a 'DenotationContext'.
-- @object@ is existentially quantified, so the only thing that can be done with it,
-- is turning it into a 'Term' using '_denotationToTerm'.
data DenotationContextMember uni res =
    forall object. DenotationContextMember (Denotation uni object res)

-- | A context of 'DenotationContextMember's.
-- Each row is a mapping from a type to a list of things that can return that type.
-- For example it can contain a mapping from @integer@ to
--   1. a bound variable of type @integer@
--   2. a bound variable of functional type with the result being @integer@
--   3. the 'AddInteger' 'BuiltinName' or any other 'BuiltinName' which returns an @integer@.
newtype DenotationContext uni = DenotationContext
    { unDenotationContext :: DMap (AsKnownType uni) (Compose [] (DenotationContextMember uni))
    }

-- Here the only search that we need to perform is the search for things that return an appropriate
-- @r@, be they variables or functions. Better if we also take types of arguments into account,
-- but it is not required as we can always generate an argument out of thin air in a rank-0 setting
-- (without @Void@).

-- | The resulting type of a 'TypeScheme'.
typeSchemeResult :: TypeScheme uni args res -> AsKnownType uni res
typeSchemeResult (TypeSchemeResult _)       = AsKnownType
typeSchemeResult (TypeSchemeArrow _ schB)   = typeSchemeResult schB
typeSchemeResult (TypeSchemeAllType _ schK) = typeSchemeResult $ schK Proxy

-- | Get the 'Denotation' of a variable.
denoteVariable :: KnownType uni res => Name -> res -> Denotation uni Name res
denoteVariable name meta = Denotation name (Var ()) meta (TypeSchemeResult Proxy)



{- The code below takes a type scheme of the form

      forall a1 ... forall aK . ty1 -> ... -> tyN -> resultTy

   (possibly K and/or N are 0) and returns lists of TyVarDecls and
   TyVars to be used to wrap a builtin application in a sequence of
   lambda abstractions and type abstractions.  It actually returns a
   Maybe, failing if the type scheme is of the wrong form.  This can
   probably be done a lot more cleanly.
-}
type TypeComponents uni = ([TyVarDecl TyName ()], [VarDecl TyName Name uni ()])

splitTypeScheme :: TypeScheme uni args res -> Quote (Maybe (TypeComponents uni))
splitTypeScheme = split1 []
    where mkVd :: Type TyName uni () -> Quote (VarDecl TyName Name uni ())
          mkVd ty = do
            u <- freshUnique
            let argname = Name (append (pack "arg") (pack . show . unUnique $ u)) u
            -- FIXME: this is making the unique explicit in the
            -- variable name, since otherwise `plc example` gives you
            -- examples where builtins take lots of arguments with the
            -- same name.
            pure $ VarDecl () argname ty

          split1 :: [TyVarDecl TyName ()] -> TypeScheme uni args res -> Quote (Maybe (TypeComponents uni))
          split1 tvds (TypeSchemeResult _)           = pure $ Just (reverse tvds, []) -- Only type variables, no types
          split1 tvds (TypeSchemeArrow tyA schB)     = do
            vd <- mkVd $ toTypeAst tyA
            split2 tvds [vd] schB  -- At the end of the type variables, look for types
          split1 tvds (TypeSchemeAllType proxy schK) = -- Found a type variable
              case proxy of
                (_ :: Proxy '(text, uniq)) ->
                    let text = pack $ symbolVal @text Proxy
                        uniq = fromIntegral $ natVal @uniq Proxy  -- Can we just make a new unique here?
                        a    = TyName $ Name text $ Unique uniq
                        tvd = TyVarDecl () a (Type ()) -- FIXME: will we ever need a higher kind here?
                    in split1 (tvd : tvds) (schK Proxy)

          split2 :: [TyVarDecl TyName ()] -> [VarDecl TyName Name uni ()] -> TypeScheme uni args res -> Quote (Maybe (TypeComponents uni))
          split2 tvds vds (TypeSchemeResult _)       = pure $ Just (reverse tvds, reverse vds)  -- Nothing left
          split2 tvds vds (TypeSchemeArrow tyA schB) = do  -- Found a type
            vd <- mkVd $ toTypeAst tyA
            split2 tvds (vd : vds) schB
          split2 _ _ (TypeSchemeAllType _ _ )         = pure Nothing  -- Found a type variable after a type

{- Since built-in names don't make sense on their own, we produce a term
   which wraps the name in a sequence of abstractions and lambdas and
   then applies the name to the relevant types and variables. This
   isn't ideal, but it does what's required for testing.

   Problem: when we call splitTypeScheme it generates uniques, but
   every time we call it it starts again at 0.  This can cause
   problems if we have nested applications of builtins (I think this
   happens in the `IfIntegers` example, causing `plc example -a` to
   fail occasionally).  [Although looking at it again, maybe that's
   not what's causing the problem.]

   Do we have to make lots more stuff run in the Quote monad to fix this?
-}
builtinNameToTerm :: TypeScheme uni args res -> StaticBuiltinName -> Term TyName Name uni ()
builtinNameToTerm scheme name =
    case runQuote $ splitTypeScheme scheme of
      Nothing -> Prelude.error "Malformed type scheme in denoteTypedBuiltinName"  -- FIXME: proper error.
      Just (tvds, vds) ->
          let tyArgs     = map (TyVar () . tyVarDeclName) tvds
              termArgs   = map (Var () . varDeclName) vds
          in mkIterTyAbs tvds (mkIterLamAbs vds (ApplyBuiltin () (StaticBuiltinName name) tyArgs termArgs))

-- | Get the 'Denotation' of a 'TypedBuiltinName'.
denoteTypedBuiltinName
    :: TypedBuiltinName uni args res -> FoldArgs args res -> Denotation uni StaticBuiltinName res
denoteTypedBuiltinName (TypedBuiltinName name scheme) meta =
    Denotation name (builtinNameToTerm scheme) meta scheme

-- | Insert the 'Denotation' of an object into a 'DenotationContext'.
insertDenotation
    :: (GShow uni, KnownType uni res)
    => Denotation uni object res -> DenotationContext uni -> DenotationContext uni
insertDenotation denotation (DenotationContext vs) = DenotationContext $
    DMap.insertWith'
        (\(Compose xs) (Compose ys) -> Compose $ xs ++ ys)
        AsKnownType
        (Compose [DenotationContextMember denotation])
        vs

-- | Insert a variable into a 'DenotationContext'.
insertVariable
    :: (GShow uni, KnownType uni a)
    => Name -> a -> DenotationContext uni -> DenotationContext uni
insertVariable name = insertDenotation . denoteVariable name

-- | Insert a 'TypedBuiltinName' into a 'DenotationContext'.
insertTypedBuiltinName
    :: GShow uni
    => TypedBuiltinName uni args res
    -> FoldArgs args res
    -> DenotationContext uni
    -> DenotationContext uni
insertTypedBuiltinName tbn@(TypedBuiltinName _ scheme) meta =
    case typeSchemeResult scheme of
        AsKnownType -> insertDenotation (denoteTypedBuiltinName tbn meta)

-- Builtins that may fail are commented out, because we cannot handle them right now.
-- Look for "UNDEFINED BEHAVIOR" in "Language.PlutusCore.Generators.Internal.Dependent".
-- | A 'DenotationContext' that consists of 'TypedBuiltinName's.
typedBuiltinNames
    :: (GShow uni, GEq uni, DefaultUni <: uni)
    => DenotationContext uni
typedBuiltinNames
    = insertTypedBuiltinName typedAddInteger           (+)
    . insertTypedBuiltinName typedSubtractInteger      (-)
    . insertTypedBuiltinName typedMultiplyInteger      (*)
--     . insertTypedBuiltinName typedDivideInteger        (nonZeroArg div)
--     . insertTypedBuiltinName typedRemainderInteger     (nonZeroArg rem)
--     . insertTypedBuiltinName typedQuotientInteger      (nonZeroArg quot)
--     . insertTypedBuiltinName typedModInteger           (nonZeroArg mod)
    . insertTypedBuiltinName typedLessThanInteger      (<)
    . insertTypedBuiltinName typedLessThanEqInteger    (<=)
    . insertTypedBuiltinName typedGreaterThanInteger   (>)
    . insertTypedBuiltinName typedGreaterThanEqInteger (>=)
    . insertTypedBuiltinName typedEqInteger            (==)
    . insertTypedBuiltinName typedConcatenate          (coerce BSL.append)
    . insertTypedBuiltinName typedTakeByteString       (coerce BSL.take . integerToInt64)
    . insertTypedBuiltinName typedDropByteString       (coerce BSL.drop . integerToInt64)
    . insertTypedBuiltinName typedSHA2                 (coerce Hash.sha2)
    . insertTypedBuiltinName typedSHA3                 (coerce Hash.sha3)
--     . insertTypedBuiltinName typedVerifySignature      verifySignature
    . insertTypedBuiltinName typedEqByteString         (==)
    $ DenotationContext mempty
