{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module PlutusTx.Test.Util.Apply (
  CompiledCodeFuncToHaskType,
  FinalType,
  compiledCodeToHaskUnsafe,
  compiledCodeToHask,
  ) where

import Prelude

import Flat (Flat)
import PlutusCore qualified as PLC
import PlutusCore.Pretty (Pretty, PrettyBy, PrettyConst, RenderContext)
import PlutusTx.Code

type family CompiledCodeFuncToHaskType t r where
  CompiledCodeFuncToHaskType (CompiledCodeIn uni fun (a -> b)) r =
    CompiledCodeIn uni fun a -> CompiledCodeFuncToHaskType (CompiledCodeIn uni fun b) r
  CompiledCodeFuncToHaskType (CompiledCodeIn uni fun a) r = r

type family FinalType t where
  FinalType (a -> b) = FinalType b
  FinalType a = a

class CompiledCodeFuncToHask t r uni fun where
  compiledCodeToHask'
    :: (Either String (CompiledCodeIn uni fun (FinalType t)) -> r)
    -> Either String (CompiledCodeIn uni fun t)
    -> CompiledCodeFuncToHaskType (CompiledCodeIn uni fun t) r

instance {-# OVERLAPPING #-} ( PLC.Everywhere uni Flat
         , PLC.Everywhere uni PrettyConst
         , PLC.Closed uni
         , Flat fun
         , Pretty fun
         , PrettyBy RenderContext (PLC.SomeTypeIn uni)
         , CompiledCodeFuncToHask b r uni fun
         , CompiledCodeFuncToHaskType (CompiledCodeIn uni fun (a -> b)) r
           ~ (CompiledCodeIn uni fun a -> CompiledCodeFuncToHaskType (CompiledCodeIn uni fun b) r)
         ) =>
  CompiledCodeFuncToHask (a -> b) r uni fun where
  compiledCodeToHask' cont f a =
    compiledCodeToHask' @b @r cont $ f >>= flip applyCode a

instance
  ( FinalType a ~ a
  , CompiledCodeFuncToHaskType (CompiledCodeIn uni fun a) r ~ r
  ) => CompiledCodeFuncToHask a r uni fun where
  compiledCodeToHask' = ($)

{- | Transform 'CompiledCode' function into a function in "Hask". This helps applying
arguments to already built script in a type safe manner. Example:
```hs
foo :: CompiledCode (Integer -> () -> Bool)
bar :: CompiledCode Integer
baz :: CompiledCode ()

compiledCodeToHask foo bar baz :: Either String (CompiledCode ())
```
-}
compiledCodeToHask
  :: forall uni fun a
   . CompiledCodeFuncToHask a (Either String (CompiledCodeIn uni fun (FinalType a))) uni fun
  => CompiledCodeIn uni fun a
  -> CompiledCodeFuncToHaskType
       (CompiledCodeIn uni fun a)
       (Either String (CompiledCodeIn uni fun (FinalType a)))
compiledCodeToHask =
  compiledCodeToHask'
    @a @(Either String (CompiledCodeIn uni fun (FinalType a)))
    id
    . pure

-- | Same as 'compiledCodeToHask' but is partial instead of returning `Either String`.
compiledCodeToHaskUnsafe
  :: forall uni fun a
   . CompiledCodeFuncToHask a (CompiledCodeIn uni fun (FinalType a)) uni fun
  => CompiledCodeIn uni fun a
  -> CompiledCodeFuncToHaskType (CompiledCodeIn uni fun a) (CompiledCodeIn uni fun (FinalType a))
compiledCodeToHaskUnsafe =
  compiledCodeToHask'
    @a @(CompiledCodeIn uni fun (FinalType a))
    (either error id)
    . pure
