-- | Kind/type inference/checking.

{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}
module Language.PlutusCore.TypeCheck
    (
    -- * Configuration.
      DynamicBuiltinNameTypes (..)
    , TypeCheckConfig (..)
    , tccDynamicBuiltinNameTypes
    , defConfig
    , dynamicBuiltinNameMeaningsToTypes
    -- * Kind/type inference/checking.
    , inferKind
    , checkKind
    , typeOfStaticBuiltinName
    , inferType
    , checkType
    , inferTypeOfProgram
    , checkTypeOfProgram
    ) where

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Core
import           Language.PlutusCore.Error
import           Language.PlutusCore.Name
import           Language.PlutusCore.Normalize
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Rename
import           Language.PlutusCore.TypeCheck.Internal
import           Language.PlutusCore.Universe

import           Control.Monad.Except

-- | The default 'TypeCheckConfig'.
defConfig :: TypeCheckConfig uni
defConfig = TypeCheckConfig mempty

-- | Extract the 'TypeScheme' from a 'DynamicBuiltinNameMeaning' and convert it to the
-- corresponding @Type TyName@ for each row of a 'DynamicBuiltinNameMeanings'.
dynamicBuiltinNameMeaningsToTypes
    :: (AsTypeError e (Term TyName Name uni ()) uni ann, MonadError e m, MonadQuote m, UniOf term ~ uni)
    => ann -> DynamicBuiltinNameMeanings term -> m (DynamicBuiltinNameTypes uni)
dynamicBuiltinNameMeaningsToTypes ann (DynamicBuiltinNameMeanings means) = do
    let getType mean = do
            let ty = dynamicBuiltinNameMeaningToType mean
            _ <- inferKind defConfig $ ann <$ ty
            pure <$> normalizeType ty
    DynamicBuiltinNameTypes <$> traverse getType means

-- | Infer the kind of a type.
inferKind
    :: (AsTypeError e term uni ann, MonadError e m, MonadQuote m)
    => TypeCheckConfig uni -> Type TyName uni ann -> m (Kind ())
inferKind config = runTypeCheckM config . inferKindM

-- | Check a type against a kind.
-- Infers the kind of the type and checks that it's equal to the given kind
-- throwing a 'TypeError' (annotated with the value of the @ann@ argument) otherwise.
checkKind
    :: (AsTypeError e term uni ann, MonadError e m, MonadQuote m)
    => TypeCheckConfig uni -> ann -> Type TyName uni ann -> Kind () -> m ()
checkKind config ann ty = runTypeCheckM config . checkKindM ann ty

-- | Infer the type of a term.
inferType
    :: ( AsTypeError e (Term TyName Name uni ()) uni ann, MonadError e m, MonadQuote m
       , GShow uni, GEq uni, DefaultUni <: uni
       )
    => TypeCheckConfig uni -> Term TyName Name uni ann -> m (Normalized (Type TyName uni ()))
inferType config = rename >=> runTypeCheckM config . inferTypeM

-- | Check a term against a type.
-- Infers the type of the term and checks that it's equal to the given type
-- throwing a 'TypeError' (annotated with the value of the @ann@ argument) otherwise.
checkType
    :: ( AsTypeError e (Term TyName Name uni ()) uni ann, MonadError e m, MonadQuote m
       , GShow uni, GEq uni, DefaultUni <: uni
       )
    => TypeCheckConfig uni
    -> ann
    -> Term TyName Name uni ann
    -> Normalized (Type TyName uni ())
    -> m ()
checkType config ann term ty = do
    termRen <- rename term
    runTypeCheckM config $ checkTypeM ann termRen ty

-- | Infer the type of a program.
inferTypeOfProgram
    :: ( AsTypeError e (Term TyName Name uni ()) uni ann, MonadError e m, MonadQuote m
       , GShow uni, GEq uni, DefaultUni <: uni
       )
    => TypeCheckConfig uni -> Program TyName Name uni ann -> m (Normalized (Type TyName uni ()))
inferTypeOfProgram config (Program _ _ term) = inferType config term

-- | Check a program against a type.
-- Infers the type of the program and checks that it's equal to the given type
-- throwing a 'TypeError' (annotated with the value of the @ann@ argument) otherwise.
checkTypeOfProgram
    :: ( AsTypeError e (Term TyName Name uni ()) uni ann, MonadError e m, MonadQuote m
       , GShow uni, GEq uni, DefaultUni <: uni
       )
    => TypeCheckConfig uni
    -> ann
    -> Program TyName Name uni ann
    -> Normalized (Type TyName uni ())
    -> m ()
checkTypeOfProgram config ann (Program _ _ term) = checkType config ann term
