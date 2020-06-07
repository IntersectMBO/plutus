{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TypeApplications #-}

module Language.PlutusCore.Constant.Embed
    ( embedStaticBuiltinNameInTerm
    , embedDynamicBuiltinNameInTerm
    )
where

import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Core
import           Language.PlutusCore.Core.Type
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Universe

import           Data.Proxy
import           Data.Text                          (append, pack)
import           GHC.TypeLits


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
            -- This makes the unique explicit in the variable name.
            -- If you don't do this then `plc example` outputs
            -- examples where builtins are applied to multiple
            -- arguments with the same name.
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
                        uniq = fromIntegral $ natVal @uniq Proxy
                        a    = TyName $ Name text $ Unique uniq
                        tvd = TyVarDecl () a (Type ())
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
-}
embedBuiltinNameInTerm :: TypeScheme uni args res -> BuiltinName -> Term TyName Name uni ()
embedBuiltinNameInTerm scheme name =
    case runQuote $ splitTypeScheme scheme of
      Nothing -> Prelude.error "Malformed type scheme in denoteTypedBuiltinName"  -- FIXME: proper error.
      Just (tvds, vds) ->
          let tyArgs     = map (TyVar () . tyVarDeclName) tvds
              termArgs   = map (Var () . varDeclName) vds
          in mkIterTyAbs tvds (mkIterLamAbs vds (ApplyBuiltin () name tyArgs termArgs))

embedStaticBuiltinNameInTerm :: TypeScheme uni args res -> StaticBuiltinName -> Term TyName Name uni ()
embedStaticBuiltinNameInTerm sch = embedBuiltinNameInTerm sch . StaticBuiltinName

embedDynamicBuiltinNameInTerm :: TypeScheme uni args res -> DynamicBuiltinName -> Term TyName Name uni ()
embedDynamicBuiltinNameInTerm sch = embedBuiltinNameInTerm sch . DynBuiltinName

