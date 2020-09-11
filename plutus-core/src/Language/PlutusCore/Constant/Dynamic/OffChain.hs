{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}

module Language.PlutusCore.Constant.Dynamic.OffChain
    ( getStringBuiltinMeanings
    , getStringBuiltinTypes
    ) where

import           Language.PlutusCore.Constant.Dynamic.BuiltinName
import           Language.PlutusCore.Constant.Function
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Core
import           Language.PlutusCore.Error
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.TypeCheck
import           Language.PlutusCore.Universe

import           Control.Monad.Except

getStringBuiltinMeanings
    :: forall term uni.
       (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` [String, Char, ()])
    => DynamicBuiltinNameMeanings term
getStringBuiltinMeanings =
       insertDynamicBuiltinNameDefinition dynamicTraceDefinitionMock $
       insertDynamicBuiltinNameDefinition dynamicCharToStringDefinition $
       insertDynamicBuiltinNameDefinition dynamicAppendDefinition mempty

getStringBuiltinTypes
    :: forall uni ann e m.
       ( AsTypeError e (Term TyName Name uni ()) uni ann, MonadError e m, MonadQuote m
       , GShow uni, GEq uni, uni `IncludesAll` '[String, Char, ()]
       )
    => ann -> m (DynamicBuiltinNameTypes uni)
getStringBuiltinTypes ann =
       dynamicBuiltinNameMeaningsToTypes ann $ getStringBuiltinMeanings @(Term TyName Name uni ())
