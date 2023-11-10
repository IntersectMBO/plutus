-- | Kind/type inference/checking.

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies    #-}

module PlutusCore.TypeCheck
    ( ToKind
    , MonadKindCheck
    , MonadTypeCheck
    , Typecheckable
    -- * Configuration.
    , BuiltinTypes (..)
    , KindCheckConfig (..)
    , TypeCheckConfig (..)
    , tccBuiltinTypes
    , defKindCheckConfig
    , builtinMeaningsToTypes
    , getDefTypeCheckConfig
    -- * Kind/type inference/checking.
    , inferKind
    , checkKind
    , inferType
    , checkType
    , inferTypeOfProgram
    , checkTypeOfProgram
    ) where

import PlutusPrelude

import PlutusCore.Builtin
import PlutusCore.Core
import PlutusCore.Default
import PlutusCore.Name
import PlutusCore.Normalize
import PlutusCore.Quote
import PlutusCore.Rename
import PlutusCore.TypeCheck.Internal

-- | The constraint for built-in types/functions are kind/type-checkable.
--
-- We keep this separate from 'MonadKindCheck'/'MonadTypeCheck', because those mainly constrain the
-- monad and 'Typecheckable' constraints only the builtins. In particular useful when the monad gets
-- instantiated and builtins don't. Another reason is that 'Typecheckable' is not required during
-- type checking, since it's only needed for computing 'BuiltinTypes', which is passed as a regular
-- argument to the worker of the type checker.
type Typecheckable uni fun = (ToKind uni, HasUniApply uni, ToBuiltinMeaning uni fun)

-- | The default kind checking config.
defKindCheckConfig :: KindCheckConfig
defKindCheckConfig = KindCheckConfig DetectNameMismatches

-- | Extract the 'TypeScheme' from a 'BuiltinMeaning' and convert it to the
-- corresponding 'Type' for each built-in function.
builtinMeaningsToTypes
    :: (MonadKindCheck err term uni fun ann m, Typecheckable uni fun)
    => BuiltinSemanticsVariant fun
    -> ann
    -> m (BuiltinTypes uni fun)
builtinMeaningsToTypes semvar ann =
    runQuoteT . fmap BuiltinTypes . sequence . tabulateArray $ \fun -> do
        let ty = typeOfBuiltinFunction semvar fun
        _ <- inferKind defKindCheckConfig $ ann <$ ty
        dupable <$> normalizeType ty

-- | Get the default type checking config.
getDefTypeCheckConfig
    :: (MonadKindCheck err term uni fun ann m, Typecheckable uni fun)
    => ann -> m (TypeCheckConfig uni fun)
getDefTypeCheckConfig ann =
    TypeCheckConfig defKindCheckConfig <$> builtinMeaningsToTypes def ann

-- | Infer the kind of a type.
inferKind
    :: MonadKindCheck err term uni fun ann m
    => KindCheckConfig -> Type TyName uni ann -> m (Kind ())
inferKind config = runTypeCheckM config . inferKindM

-- | Check a type against a kind.
-- Infers the kind of the type and checks that it's equal to the given kind
-- throwing a 'TypeError' (annotated with the value of the @ann@ argument) otherwise.
checkKind
    :: MonadKindCheck err term uni fun ann m
    => KindCheckConfig -> ann -> Type TyName uni ann -> Kind () -> m ()
checkKind config ann ty = runTypeCheckM config . checkKindM ann ty

-- | Infer the type of a term.
inferType
    :: MonadTypeCheckPlc err uni fun ann m
    => TypeCheckConfig uni fun
    -> Term TyName Name uni fun ann
    -> m (Normalized (Type TyName uni ()))
inferType config = rename >=> runTypeCheckM config . inferTypeM

-- | Check a term against a type.
-- Infers the type of the term and checks that it's equal to the given type
-- throwing a 'TypeError' (annotated with the value of the @ann@ argument) otherwise.
checkType
    :: MonadTypeCheckPlc err uni fun ann m
    => TypeCheckConfig uni fun
    -> ann
    -> Term TyName Name uni fun ann
    -> Normalized (Type TyName uni ())
    -> m ()
checkType config ann term ty = do
    termRen <- rename term
    runTypeCheckM config $ checkTypeM ann termRen ty

-- | Infer the type of a program.
inferTypeOfProgram
    :: MonadTypeCheckPlc err uni fun ann m
    => TypeCheckConfig uni fun
    -> Program TyName Name uni fun ann
    -> m (Normalized (Type TyName uni ()))
inferTypeOfProgram config (Program _ _ term) = inferType config term

-- | Check a program against a type.
-- Infers the type of the program and checks that it's equal to the given type
-- throwing a 'TypeError' (annotated with the value of the @ann@ argument) otherwise.
checkTypeOfProgram
    :: MonadTypeCheckPlc err uni fun ann m
    => TypeCheckConfig uni fun
    -> ann
    -> Program TyName Name uni fun ann
    -> Normalized (Type TyName uni ())
    -> m ()
checkTypeOfProgram config ann (Program _ _ term) = checkType config ann term
