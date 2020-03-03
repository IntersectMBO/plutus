{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TypeOperators       #-}

module Language.PlutusCore.Constant.Dynamic.OnChain
    ( OnChain (..)
    , OnChainEvaluator
    , OnChainTransformer
    , OnChainHandler
    , mangleOnChain
    , handleDynamicByMeaning
    , dynamicEmit
    , handleDynamicEmit
    , dynamicLog
    , handleDynamicLog
    , evaluateHandlersBy
    ) where

import           Language.PlutusCore.Constant.Dynamic.Call
import           Language.PlutusCore.Constant.Dynamic.Emit
import           Language.PlutusCore.Constant.Dynamic.Instances     ()
import           Language.PlutusCore.Constant.Function
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Universe

import           Control.Exception
import           Data.Coerce
import qualified Data.Kind                                          as GHC (Type)
import           Data.Proxy
import qualified Data.Text                                          as Text
import           GHC.TypeLits

{- Note [Interpretation of names]
The thing about dynamic built-in names is that they really can denote arbitrary effects.
This means we can't just initialize an evaluator with a 'DynamicBuiltinNameMeanings', because
some of these 'DynamicBuiltinNameMeaning's may be initializable in monads, some of them may call
effectful functions during evaluation (but we use 'unsafePerformIO' to handle this case for now),
but what's worse is that some of them may require finalization. This means we can't even pass a
@m DynamicBuiltinNameMeaning@ to an evaluator, we have to do something *after* evaluation finishes.
And of course the evaluator can't know everything we may want to do. In general, we want a way to
interpret dynamic built-in names in such a way that intepretation alters the process of evaluation.
Like if you want logging, then you need to open something to write logs in before evaluation starts
and to read the logs after evaluation finishes. But it is also the case that many dynamic built-in
names are perfectly pure, so we need an interface that allows to compose various kinds of handlers
of dynamic built-in names. And "handler" is a very right word, because what we do in this file is
very similar to how handlers of algebraic effects work.
-}

{- Note [Names at the type-level]
Due to the fact that the interpretation of a dynamic built-in name is an arbitrary effect, we must know
beforehand names that a term contains, because the type of the result of evaluation depends on them.
An on-chain evaluator knows how to evaluate certain names, but terms are generated off-chain meaning
the on-chain evaluator and the off-chain generator must have consensus on which names what mean.
For this reason we index an on-chain term by a list of dynamic built-in names it can contain.
Any generator targeting a certain blockchain must produce terms indexed by names the blockchain is able
to evaluate.
-}

-- Well that's ugly.
newtype OnChain (names :: [Symbol]) f (tyname :: GHC.Type -> GHC.Type) (name :: GHC.Type -> GHC.Type) (uni :: GHC.Type -> GHC.Type) ann = OnChain
    { unOnChain :: f tyname name uni ann
    }

-- Does it make sense to unify this with 'Evaluator' somehow?
-- Is it really worth parameterizing this by 'f', so that is can be used over both
-- 'Term' and 'Program'? I imagine we can live with just 'Term'.
-- | The type of evaluators that run on-chain. This is very similar to 'Evaluator', except
-- an 'OnChainEvaluator' is allowed to return any @r@, not just a @m EvaluationResult@ for some @m@.
-- This is because an evaluator running on-chain can perform arbitrary effects and return an arbitrary
-- result containing an 'EvaluationResult' somewhere deep inside @r@.
type OnChainEvaluator names f uni r =
    DynamicBuiltinNameMeanings uni -> OnChain names f TyName Name uni () -> r

-- @f@ is shared, hence it does first.
-- | The type of functions that transform 'OnChainEvaluator's.
type OnChainTransformer f names r names' uni r' =
    OnChainEvaluator names f uni r -> OnChainEvaluator names' f uni r'

-- | The type of handlers of outermost dynamic built-in names.
type OnChainHandler name f uni r s =
    forall names. OnChainTransformer f names r (name ': names) uni s

mangleOnChain :: OnChain names f tyname name uni ann -> OnChain names' f tyname name uni ann
mangleOnChain = coerce

-- We should connect names with their meanings at the type level: @DynamicBuiltinNameMeaningOf name@.
-- Maybe we should even use dependent maps in abstract machines. Though, they are probably
-- not as optimized.
-- | Interpret a 'DynamicBuiltinNameMeaning' as an 'OnChainHandler' that doesn't change
-- the resulting type of evaluation.
handleDynamicByMeaning
    :: forall name f uni r. KnownSymbol name
    => DynamicBuiltinNameMeaning uni -> OnChainHandler name f uni r r
handleDynamicByMeaning mean eval env = eval env' . mangleOnChain where
    name    = DynamicBuiltinName . Text.pack $ symbolVal (Proxy :: Proxy name)
    nameDef = DynamicBuiltinNameDefinition name mean
    env'    = insertDynamicBuiltinNameDefinition nameDef env

handleDynamicEmitter
    :: forall name f uni r. (GShow uni, GEq uni, uni `Includes` Integer, KnownSymbol name)
    => OnChainHandler name f uni r (forall a. KnownType uni a => IO ([a], r))
handleDynamicEmitter eval env term = withEmit $ \emit -> do
    let emitName = DynamicBuiltinName . Text.pack $ symbolVal (Proxy :: Proxy name)
        emitDef  = dynamicCallAssign emitName emit (\_ -> ExBudget 1 1) -- TODO
        env' = insertDynamicBuiltinNameDefinition emitDef env
    evaluate . eval env' $ mangleOnChain term

dynamicEmit :: Term tyname name uni ()
dynamicEmit = dynamicBuiltinNameAsTerm $ DynamicBuiltinName "emit"

handleDynamicEmit
    :: (GShow uni, GEq uni, uni `Includes` Integer)
    => OnChainHandler "emit" f uni r (forall a. KnownType uni a => IO ([a], r))
handleDynamicEmit = handleDynamicEmitter

dynamicLog :: Term tyname name uni ()
dynamicLog = dynamicBuiltinNameAsTerm $ DynamicBuiltinName "log"

handleDynamicLog
    :: (GShow uni, GEq uni, uni `Includes` Integer, uni `Includes` String)
    => OnChainHandler "log" f uni r (IO ([String], r))
handleDynamicLog = handleDynamicEmitter

evaluateHandlersBy
    :: AnEvaluator f uni m b
    -> (AnEvaluator (OnChain '[] f) uni m b -> OnChainEvaluator names f uni r)
    -> OnChain names f TyName Name uni ()
    -> r
evaluateHandlersBy eval handlers = handlers (\means -> eval means . unOnChain) mempty

-- We could have this class just to ensure that names are globally unique, but any instance
-- is necessary orphan which defeats the entire purpose.
-- class GlobalBuiltinName (name :: Symbol) m | name -> m where
--     handleGlobalBuiltinNameM :: OnChainHandler f name r (m r)
