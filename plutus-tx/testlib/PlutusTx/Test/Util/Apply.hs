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
  unsafeApplyCodeN,
  applyCodeN,
  ) where

import Prelude

import PlutusCore qualified as PLC
import PlutusCore.Flat (Flat)
import PlutusCore.Pretty (Pretty, PrettyBy, PrettyConst, RenderContext, pretty)
import PlutusTx.Code
import PlutusIR.Error

type family CompiledCodeFuncToHaskType t r where
  CompiledCodeFuncToHaskType (CompiledCodeIn uni fun (a -> b)) r =
    CompiledCodeIn uni fun a -> CompiledCodeFuncToHaskType (CompiledCodeIn uni fun b) r
  CompiledCodeFuncToHaskType (CompiledCodeIn uni fun a) r = r

type family FinalType t where
  FinalType (a -> b) = FinalType b
  FinalType a = a

class CompiledCodeFuncToHask t r uni fun where
  applyCodeN'
    :: (Either (Error uni fun PLC.SrcSpans) (CompiledCodeIn uni fun (FinalType t)) -> r)
    -> Either (Error uni fun PLC.SrcSpans) (CompiledCodeIn uni fun t)
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
  applyCodeN' cont f a =
    applyCodeN' @b @r cont $ f >>= flip safeApplyCode a

instance
  ( FinalType a ~ a
  , CompiledCodeFuncToHaskType (CompiledCodeIn uni fun a) r ~ r
  ) => CompiledCodeFuncToHask a r uni fun where
  applyCodeN' = ($)

{- | Transform 'CompiledCode' function into a function in "Hask". This helps applying
arguments to already built script in a type safe manner. Example:
```hs
foo :: CompiledCode (Integer -> () -> Bool)
bar :: CompiledCode Integer
baz :: CompiledCode ()

applyCodeN foo bar baz :: Either (Error uni fun SrcSpans) (CompiledCode Bool)
```
-}
applyCodeN
  :: forall uni fun a
   . CompiledCodeFuncToHask a (Either (Error uni fun PLC.SrcSpans) (CompiledCodeIn uni fun (FinalType a))) uni fun
  => CompiledCodeIn uni fun a
  -> CompiledCodeFuncToHaskType
       (CompiledCodeIn uni fun a)
       (Either (Error uni fun PLC.SrcSpans) (CompiledCodeIn uni fun (FinalType a)))
applyCodeN =
  applyCodeN'
    @a @(Either (Error uni fun PLC.SrcSpans) (CompiledCodeIn uni fun (FinalType a)))
    id
    . pure

-- | Same as 'applyCodeN' but is partial instead of returning `Either (Error uni fun SrcSpans)`.
unsafeApplyCodeN
  :: forall uni fun a
   . ( CompiledCodeFuncToHask a (CompiledCodeIn uni fun (FinalType a)) uni fun
     , PLC.Everywhere uni PrettyConst
     , PrettyBy RenderContext (PLC.SomeTypeIn uni)
     , PLC.Closed uni, Pretty fun
     )
  => CompiledCodeIn uni fun a
  -> CompiledCodeFuncToHaskType (CompiledCodeIn uni fun a) (CompiledCodeIn uni fun (FinalType a))
unsafeApplyCodeN =
  applyCodeN'
    @a @(CompiledCodeIn uni fun (FinalType a))
    (either (error . show . pretty) id)
    . pure
