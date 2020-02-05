-- | Smart constructors of PLC constants.

{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Language.PlutusCore.Constant.Make
    ( builtinNameAsTerm
    , dynamicBuiltinNameAsTerm
    , makeTyBuiltin
    , makeConstant
    ) where

import           Language.PlutusCore.Constant.Universe
import           Language.PlutusCore.Core
import           Language.PlutusCore.MkPlc

-- | Lift a 'BuiltinName' to 'Term'.
builtinNameAsTerm :: TermLike term tyname name uni => BuiltinName -> term ()
builtinNameAsTerm = builtin () . BuiltinName ()

-- | Lift a 'DynamicBuiltinName' to 'Term'.
dynamicBuiltinNameAsTerm :: TermLike term tyname name uni => DynamicBuiltinName -> term ()
dynamicBuiltinNameAsTerm = builtin () . DynBuiltinName ()

makeTyBuiltin
    :: forall a uni tyname. uni `Includes` a
    => Type tyname uni ()
makeTyBuiltin = TyBuiltin () . Some $ knownUni @uni @a

-- | Wrap a Haskell value as a PLC term.
makeConstant
    :: forall a uni term tyname name. (TermLike term tyname name uni, uni `Includes` a)
    => a -> term ()
makeConstant = constant () . SomeOf knownUni
