-- | Kind/type inference/checking.

module Language.PlutusCore.TypeCheck
    (
    -- * Configuration.
      DynamicBuiltinNameTypes (..)
    , TypeCheckConfig (..)
    , tccDoNormTypes
    , tccDynamicBuiltinNameTypes
    , tccMayGas
    , defTypeCheckGas
    , onChainConfig
    , offChainConfig
    , defOnChainConfig
    , defOffChainConfig
    , dynamicBuiltinNameMeaningsToTypes
    -- * Kind/type inference/checking.
    , kindOfTypeBuiltin
    , inferKind
    , checkKind
    , typeOfBuiltinName
    , inferType
    , checkType
    , inferTypeOfProgram
    , checkTypeOfProgram
    ) where

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Error
import           Language.PlutusCore.Name
import           Language.PlutusCore.Normalize
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Rename
import           Language.PlutusCore.Type
import           Language.PlutusCore.TypeCheck.Internal

import           Control.Monad.Except

-- | The default amount of gas to run the type checker with.
defTypeCheckGas :: Gas
defTypeCheckGas = Gas 1000

-- | The 'TypeCheckConfig' used on the chain.
onChainConfig :: DynamicBuiltinNameTypes -> Gas -> TypeCheckConfig
onChainConfig tys = TypeCheckConfig False tys . Just

-- | The 'TypeCheckConfig' used off the chain.
offChainConfig :: DynamicBuiltinNameTypes -> TypeCheckConfig
offChainConfig tys = TypeCheckConfig True tys Nothing

-- | The default 'TypeCheckConfig' used on the chain.
defOnChainConfig :: TypeCheckConfig
defOnChainConfig = onChainConfig mempty defTypeCheckGas

-- | The default 'TypeCheckConfig' used off the chain.
defOffChainConfig :: TypeCheckConfig
defOffChainConfig = offChainConfig mempty

-- | Extract the 'TypeScheme' from a 'DynamicBuiltinNameMeaning' and convert it to the
-- corresponding @Type TyName@ for each row of a 'DynamicBuiltinNameMeanings'.
dynamicBuiltinNameMeaningsToTypes
    :: (AsTypeError e ann, MonadError e m, MonadQuote m)
    => ann -> DynamicBuiltinNameMeanings -> m DynamicBuiltinNameTypes
dynamicBuiltinNameMeaningsToTypes ann (DynamicBuiltinNameMeanings means) = do
    let getType mean = do
            ty <- liftQuote $ dynamicBuiltinNameMeaningToType mean
            _ <- inferKind (offChainConfig mempty) $ ann <$ ty
            tyRen <- rename ty
            normalizeTypeFull tyRen
    DynamicBuiltinNameTypes <$> traverse getType means

-- | Infer the kind of a type.
inferKind
    :: (AsTypeError e ann, MonadError e m, MonadQuote m)
    => TypeCheckConfig -> Type TyName ann -> m (Kind ())
inferKind config = runTypeCheckM config . inferKindM

-- | Check a type against a kind.
-- Infers the kind of the type and checks that it's equal to the given kind
-- throwing a 'TypeError' (annotated with the value of the @ann@ argument) otherwise.
checkKind
    :: (AsTypeError e ann, MonadError e m, MonadQuote m)
    => TypeCheckConfig -> ann -> Type TyName ann -> Kind () -> m ()
checkKind config ann ty = runTypeCheckM config . checkKindM ann ty

-- | Infer the type of a term.
inferType
    :: (AsTypeError e ann, MonadError e m, MonadQuote m)
    => TypeCheckConfig -> Term TyName Name ann -> m (Normalized (Type TyName ()))
inferType config = rename >=> runTypeCheckM config . inferTypeM

-- | Check a term against a type.
-- Infers the type of the term and checks that it's equal to the given type
-- throwing a 'TypeError' (annotated with the value of the @ann@ argument) otherwise.
checkType
    :: (AsTypeError e ann, MonadError e m, MonadQuote m)
    => TypeCheckConfig -> ann -> Term TyName Name ann -> Normalized (Type TyName ()) -> m ()
checkType config ann term ty = do
    termRen <- rename term
    runTypeCheckM config $ checkTypeM ann termRen ty

-- | Infer the type of a program.
inferTypeOfProgram
    :: (AsTypeError e ann, MonadError e m, MonadQuote m)
    => TypeCheckConfig -> Program TyName Name ann -> m (Normalized (Type TyName ()))
inferTypeOfProgram config (Program _ _ term) = inferType config term

-- | Check a program against a type.
-- Infers the type of the program and checks that it's equal to the given type
-- throwing a 'TypeError' (annotated with the value of the @ann@ argument) otherwise.
checkTypeOfProgram
    :: (AsTypeError e ann, MonadError e m, MonadQuote m)
    => TypeCheckConfig -> ann -> Program TyName Name ann -> Normalized (Type TyName ()) -> m ()
checkTypeOfProgram config ann (Program _ _ term) = checkType config ann term
