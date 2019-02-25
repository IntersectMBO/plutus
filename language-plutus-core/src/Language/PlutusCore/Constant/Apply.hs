-- | Computing constant application.

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Constant.Apply
    ( ConstAppError (..)
    , ConstAppResult (..)
    , ConstAppResultDef
    , makeConstAppResult
    , applyTypeSchemed
    , applyBuiltinName
    ) where

import           Language.PlutusCore.Constant.Dynamic.Instances ()
import           Language.PlutusCore.Constant.Function
import           Language.PlutusCore.Constant.Make
import           Language.PlutusCore.Constant.Name
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Lexer.Type                 (BuiltinName (..))
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           PlutusPrelude

import           Control.Monad.Except
import           Crypto
import qualified Data.ByteString.Lazy                           as BSL
import qualified Data.ByteString.Lazy.Hash                      as Hash
import           Data.IntMap.Strict                             (IntMap)
import qualified Data.IntMap.Strict                             as IntMap
import           Data.Text                                      (Text)

-- | The type of constant applications errors.
data ConstAppError
    = SizeMismatchConstAppError Size (Constant ())
      -- ^ A mismatch between expected and actual sizes.
    | IllTypedConstAppError BuiltinSized (Constant ())
      -- ^ A mismatch between the type of an argument function expects and its actual type.
    | ExcessArgumentsConstAppError [Value TyName Name ()]
      -- ^ A constant is applied to more arguments than needed in order to reduce.
      -- Note that this error occurs even if an expression is well-typed, because
      -- constant application is supposed to be computed as soon as there are enough arguments.
    | SizedNonConstantConstAppError (Value TyName Name ())
      -- ^ An argument of a sized type is not a constant.
    | UnreadableBuiltinConstAppError (Value TyName Name ()) Text
      -- ^ Could not construct denotation for a built-in.
    deriving (Show, Eq)

-- | The type of constant applications results.
data ConstAppResult a
    = ConstAppSuccess a
      -- ^ Successfully computed a value.
    | ConstAppFailure
      -- ^ Not enough gas.
    | ConstAppStuck
      -- ^ Not enough arguments.
    | ConstAppError ConstAppError
      -- ^ An internal error occurred during evaluation.
    deriving (Show, Eq, Functor, Foldable, Traversable)

instance Applicative ConstAppResult where
    pure = ConstAppSuccess

    ConstAppSuccess f <*> a = fmap f a
    ConstAppFailure   <*> _ = ConstAppFailure
    ConstAppStuck     <*> _ = ConstAppStuck
    ConstAppError err <*> _ = ConstAppError err

instance Monad ConstAppResult where
    ConstAppSuccess x >>= f = f x
    ConstAppFailure   >>= _ = ConstAppFailure
    ConstAppStuck     >>= _ = ConstAppStuck
    ConstAppError err >>= _ = ConstAppError err

type ConstAppResultDef = ConstAppResult (Value TyName Name ())

newtype SizeVar = SizeVar Int

-- | An 'IntMap' from size variables to sizes.
newtype SizeValues = SizeValues (IntMap Size)

instance ( PrettyBy config (Constant ())
         , PrettyBy config (Value TyName Name ())
         ) => PrettyBy config ConstAppError where
    prettyBy config (SizeMismatchConstAppError expSize con)  = fold
        [ "Size mismatch error:", "\n"
        , "expected size: ", pretty expSize, "\n"
        , "actual constant: ", prettyBy config con
        ]
    prettyBy config (IllTypedConstAppError expType con)      = fold
        [ "Ill-typed constant application:", "\n"
        , "expected type: ", pretty expType, "\n"
        , "actual constant: ", prettyBy config con
        ]
    prettyBy config (ExcessArgumentsConstAppError args)      = fold
        [ "A constant applied to too many arguments:", "\n"
        , "Excess ones are: ", prettyBy config args
        ]
    prettyBy config (SizedNonConstantConstAppError arg)      = fold
        [ "A non-constant argument of a sized type: "
        , prettyBy config arg
        ]
    prettyBy config (UnreadableBuiltinConstAppError arg err) = fold
        [ "Could not construct denotation for a built-in:", "\n"
        , prettyBy config arg, "\n"
        , "The error was: "
        , pretty err
        ]

instance ( PrettyBy config (Constant ())
         , PrettyBy config (Value TyName Name ())
         , PrettyBy config a
         ) => PrettyBy config (ConstAppResult a) where
    prettyBy config (ConstAppSuccess res) = prettyBy config res
    prettyBy _      ConstAppFailure       = "Constant application failure"
    prettyBy _      ConstAppStuck         = "Stuck constant applcation"
    prettyBy config (ConstAppError err)   = prettyBy config err

instance Enum SizeVar where
    toEnum = SizeVar
    fromEnum (SizeVar sizeIndex) = sizeIndex

-- Who are you?
forBind :: (Monad m, Traversable m, Applicative f) => m a -> (a -> f (m b)) -> f (m b)
forBind a f = join <$> traverse f a

-- | Same as 'makeBuiltin', but returns a 'ConstAppResult'.
makeConstAppResult :: TypedBuiltinValue Size a -> ConstAppResultDef
makeConstAppResult = maybe ConstAppFailure ConstAppSuccess . makeBuiltin

-- | Look up a size variable in an environment.
sizeAt :: SizeVar -> SizeValues -> Size
sizeAt (SizeVar sizeIndex) (SizeValues sizes) = sizes IntMap.! sizeIndex

-- | If previously seen size is not equal to the most recently encountered,
-- then return an error, otherwise return a received value and its expected size.
checkBuiltinSize :: Maybe Size -> Size -> Constant () -> b -> ConstAppResult (b, Size)
checkBuiltinSize (Just size) size' constant _ | size /= size' =
    ConstAppError $ SizeMismatchConstAppError size constant
checkBuiltinSize  _          size' _        y =
    ConstAppSuccess (y, size')

-- | Convert a PLC constant into the corresponding Haskell value and also return its size.
-- Checks that the constant is of a given type and there are no size mismatches.
extractSizedBuiltin
    :: TypedBuiltinSized a -> Maybe Size -> Constant () -> ConstAppResult (a, Size)
extractSizedBuiltin TypedBuiltinSizedInt  maySize constant@(BuiltinInt  () size' int) =
    checkBuiltinSize maySize size' constant int
extractSizedBuiltin TypedBuiltinSizedBS   maySize constant@(BuiltinBS   () size' bs ) =
    checkBuiltinSize maySize size' constant bs
extractSizedBuiltin TypedBuiltinSizedSize maySize constant@(BuiltinSize () size'    ) =
    checkBuiltinSize maySize size' constant ()
extractSizedBuiltin tbs                   _       constant                            =
    ConstAppError $ IllTypedConstAppError (eraseTypedBuiltinSized tbs) constant

-- | Substitute the looked up 'Size' value for the size variable of a 'TypedBuiltin'.
substSizeVar :: SizeValues -> TypedBuiltin SizeVar a -> TypedBuiltin Size a
substSizeVar = mapSizeTypedBuiltin . flip sizeAt

-- TODO: rewrite me to use 'StateT'.
-- | Convert a PLC constant (unwrapped from 'Value') into the corresponding Haskell value.
-- Checks that the constant is of a given built-in type and there are no size mismatches.
-- Updates 'SizeValues' along the way, so if a new size variable is encountered,
-- it'll be added to 'SizeValues' along with its value.
extractBuiltin
    :: Monad m
    => TypedBuiltin SizeVar a
    -> SizeValues
    -> Value TyName Name ()
    -> Evaluate m (ConstAppResult (a, SizeValues))
extractBuiltin (TypedBuiltinSized sizeEntry tbs) (SizeValues sizes) value =
    return $ case value of
        Constant () constant -> case sizeEntry of
            SizeValue size                ->
                (SizeValues sizes <$) <$> extractSizedBuiltin tbs (Just size) constant
            SizeBound (SizeVar sizeIndex) ->
                unPairT . fmap SizeValues $ IntMap.alterF upd sizeIndex sizes where
                    upd maySize = fmap Just . PairT $ extractSizedBuiltin tbs maySize constant
        _                    -> ConstAppError $ SizedNonConstantConstAppError value
extractBuiltin TypedBuiltinDyn                   sizeValues         value =
    readDynamicBuiltinM value <&> \conv -> case runExceptT conv of
        EvaluationFailure            -> ConstAppFailure
        EvaluationSuccess (Left err) -> ConstAppError $ UnreadableBuiltinConstAppError value err
        EvaluationSuccess (Right x ) -> ConstAppSuccess (x, sizeValues)

-- | Convert a PLC constant (unwrapped from 'Value') into the corresponding Haskell value.
-- Checks that the constant is of a given type and there are no size mismatches.
-- Updates 'SizeValues' along the way, so if a new size variable is encountered,
-- it'll be added to 'SizeValues' along with its value.
extractSchemed
    :: Monad m
    => TypeScheme SizeVar a r
    -> SizeValues
    -> Value TyName Name ()
    -> Evaluate m (ConstAppResult (a, SizeValues))
extractSchemed (TypeSchemeBuiltin a) sizeValues value = extractBuiltin a sizeValues value
extractSchemed (TypeSchemeArrow _ _) _          _     = error "Not implemented."
extractSchemed (TypeSchemeAllSize _) _          _     = error "Not implemented."

-- | Apply a function with a known 'TypeScheme' to a list of 'Constant's (unwrapped from 'Value's).
-- Checks that the constants are of expected types and there are no size mismatches.
applyTypeSchemed
    :: Monad m
    => TypeScheme SizeVar a r -> a -> [Value TyName Name ()] -> Evaluate m ConstAppResultDef
applyTypeSchemed schema = go schema (SizeVar 0) (SizeValues mempty) where
    go
        :: Monad m
        => TypeScheme SizeVar a r
        -> SizeVar
        -> SizeValues
        -> a
        -> [Value TyName Name ()]
        -> Evaluate m ConstAppResultDef
    go (TypeSchemeBuiltin tb)      _       sizeValues y args = case args of  -- Computed the result.
        -- This is where all the size checks prescribed by the specification happen.
        -- We instantiate the size variable of a final 'TypedBuiltin' to its value and call
        -- 'makeConstAppResult' which performs the final size check before converting
        -- a Haskell value to the corresponding PLC one.
        [] -> return . makeConstAppResult $ TypedBuiltinValue (substSizeVar sizeValues tb) y
        _  -> return . ConstAppError $ ExcessArgumentsConstAppError args     -- Too many arguments.
    go (TypeSchemeArrow schA schB) sizeVar sizeValues f args = case args of
        []          -> return ConstAppStuck             -- Not enough arguments to compute.
        arg : args' -> do                               -- Peel off one argument.
            -- Coerce the argument to a Haskell value.
            res <- extractSchemed schA sizeValues arg
            forBind res $ \(x, sizeValues') ->
                -- Apply the function to the coerced argument and proceed recursively.
                go schB sizeVar sizeValues' (f x) args'
    go (TypeSchemeAllSize schK)    sizeVar sizeValues f args =
        -- Instantiate the `forall` with a fresh var and proceed recursively.
        go (schK sizeVar) (succ sizeVar) sizeValues f args

-- | Apply a 'TypedBuiltinName' to a list of 'Constant's (unwrapped from 'Value's)
-- Checks that the constants are of expected types and there are no size mismatches.
applyTypedBuiltinName
    :: Monad m
    => TypedBuiltinName a r -> a -> [Value TyName Name ()] -> Evaluate m ConstAppResultDef
applyTypedBuiltinName (TypedBuiltinName _ schema) = applyTypeSchemed schema

-- | Apply a 'TypedBuiltinName' to a list of 'Constant's (unwrapped from 'Value's)
-- Checks that the constants are of expected types and there are no size mismatches.
applyBuiltinName
    :: Monad m
    => BuiltinName -> [Value TyName Name ()] -> Evaluate m ConstAppResultDef
applyBuiltinName AddInteger           = applyTypedBuiltinName typedAddInteger           (+)
applyBuiltinName SubtractInteger      = applyTypedBuiltinName typedSubtractInteger      (-)
applyBuiltinName MultiplyInteger      = applyTypedBuiltinName typedMultiplyInteger      (*)
applyBuiltinName DivideInteger        = applyTypedBuiltinName typedDivideInteger        div
applyBuiltinName QuotientInteger      = applyTypedBuiltinName typedQuotientInteger      quot
applyBuiltinName RemainderInteger     = applyTypedBuiltinName typedRemainderInteger     rem
applyBuiltinName ModInteger           = applyTypedBuiltinName typedModInteger           mod
applyBuiltinName LessThanInteger      = applyTypedBuiltinName typedLessThanInteger      (<)
applyBuiltinName LessThanEqInteger    = applyTypedBuiltinName typedLessThanEqInteger    (<=)
applyBuiltinName GreaterThanInteger   = applyTypedBuiltinName typedGreaterThanInteger   (>)
applyBuiltinName GreaterThanEqInteger = applyTypedBuiltinName typedGreaterThanEqInteger (>=)
applyBuiltinName EqInteger            = applyTypedBuiltinName typedEqInteger            (==)
applyBuiltinName ResizeInteger        = applyTypedBuiltinName typedResizeInteger        (const id)
applyBuiltinName IntToByteString      = applyTypedBuiltinName typedIntToByteString      undefined
applyBuiltinName Concatenate          = applyTypedBuiltinName typedConcatenate          (<>)
applyBuiltinName TakeByteString       = applyTypedBuiltinName typedTakeByteString
                                                                  (BSL.take . fromIntegral)
applyBuiltinName DropByteString       = applyTypedBuiltinName typedDropByteString
                                                                  (BSL.drop . fromIntegral)
applyBuiltinName ResizeByteString     = applyTypedBuiltinName typedResizeByteString     (const id)
applyBuiltinName SHA2                 = applyTypedBuiltinName typedSHA2                 Hash.sha2
applyBuiltinName SHA3                 = applyTypedBuiltinName typedSHA3                 Hash.sha3
applyBuiltinName VerifySignature      = applyTypedBuiltinName typedVerifySignature      verifySignature
applyBuiltinName EqByteString         = applyTypedBuiltinName typedEqByteString         (==)
applyBuiltinName SizeOfInteger        = applyTypedBuiltinName typedSizeOfInteger        (const ())
