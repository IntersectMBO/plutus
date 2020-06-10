{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TypeApplications #-}

module Language.PlutusCore.Constant.Embed
    ( embedStaticBuiltinNameInTerm
    , embedTypedBuiltinNameInTerm
    , embedDynamicBuiltinNameInTerm
    )
where

import           Language.PlutusCore.Constant.Function
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Core
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote

import           Data.Text                             (append, pack)


{- | Since built-in names don't make sense on their own, we produce a
   term which wraps the name in a sequence of abstractions and lambdas
   and then applies the name to the relevant types and variables. This
   isn't ideal, but it does what's required for testing.
-}
embedBuiltinNameInTerm :: TypeScheme uni args res -> BuiltinName -> Term TyName Name uni ()
embedBuiltinNameInTerm scheme name =
    let mkVarDecl :: Type TyName uni () -> Quote (VarDecl TyName Name uni ())
        mkVarDecl ty = do
          u <- freshUnique
          let argname = Name (append (pack "arg") (pack . show . unUnique $ u)) u
          -- This makes the unique explicit in the variable name.
          -- If you don't do this then `plc example` outputs
          -- examples where builtins are applied to multiple
          -- arguments with the same name.
          pure $ VarDecl () argname ty
        mkTyVarDecl :: TyName -> TyVarDecl TyName ()
        mkTyVarDecl tyname = TyVarDecl () tyname (Type ())
    in case splitTypeScheme scheme of
      Nothing -> undefined -- Prelude.error "Malformed type scheme in denoteTypedBuiltinName"  -- FIXME: proper error.
      Just (TypeComponents tynames types _) ->
          runQuote $ do
            varDecls <- mapM mkVarDecl types  -- For each argument type, generate a VarDecl for a variable of that type
            let termArgs = map (Var () . varDeclName) varDecls
                tyArgs = map (TyVar ()) tynames
                tyVarDecls = map mkTyVarDecl tynames
            pure $ mkIterTyAbs tyVarDecls (mkIterLamAbs varDecls (ApplyBuiltin () name tyArgs termArgs))

embedStaticBuiltinNameInTerm :: TypeScheme uni args res -> StaticBuiltinName -> Term TyName Name uni ()
embedStaticBuiltinNameInTerm sch = embedBuiltinNameInTerm sch . StaticBuiltinName

embedTypedBuiltinNameInTerm :: TypedBuiltinName uni args r -> Term TyName Name uni ()
embedTypedBuiltinNameInTerm (TypedBuiltinName sbn sch) = embedStaticBuiltinNameInTerm sch sbn


embedDynamicBuiltinNameInTerm :: TypeScheme uni args res -> DynamicBuiltinName -> Term TyName Name uni ()
embedDynamicBuiltinNameInTerm sch = embedBuiltinNameInTerm sch . DynBuiltinName

