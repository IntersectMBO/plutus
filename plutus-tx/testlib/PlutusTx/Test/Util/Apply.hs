{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module PlutusTx.Test.Util.Apply
  ( CompiledCodeFuncToHaskType
  , FinalType
  , unsafeApplyCodeN
  , applyCodeN
  ) where

import Prelude

import PlutusCore qualified as PLC
import PlutusCore.Flat (Flat)
import PlutusCore.Pretty (Pretty, PrettyBy, PrettyConst, RenderContext)
import PlutusTx.Code

type family CompiledCodeFuncToHaskType t r where
  CompiledCodeFuncToHaskType (CompiledCodeIn uni fun pat (a -> b)) r =
    CompiledCodeIn uni fun pat a
    -> CompiledCodeFuncToHaskType (CompiledCodeIn uni fun pat b) r
  CompiledCodeFuncToHaskType (CompiledCodeIn uni fun pat a) r = r

type family FinalType t where
  FinalType (a -> b) = FinalType b
  FinalType a = a

class CompiledCodeFuncToHask t r uni fun pat where
  applyCodeN'
    :: (Either String (CompiledCodeIn uni fun pat (FinalType t)) -> r)
    -> Either String (CompiledCodeIn uni fun pat t)
    -> CompiledCodeFuncToHaskType (CompiledCodeIn uni fun pat t) r

instance
  {-# OVERLAPPING #-}
  ( PLC.Everywhere uni Flat
  , PLC.Everywhere uni PrettyConst
  , PLC.Closed uni
  , Flat pat
  , Flat fun
  , Pretty fun
  , PrettyBy RenderContext (PLC.SomeTypeIn uni)
  , CompiledCodeFuncToHask b r uni fun pat
  , CompiledCodeFuncToHaskType (CompiledCodeIn uni fun pat (a -> b)) r
      ~ ( CompiledCodeIn uni fun pat a
          -> CompiledCodeFuncToHaskType (CompiledCodeIn uni fun pat b) r
        )
  )
  => CompiledCodeFuncToHask (a -> b) r uni fun pat
  where
  applyCodeN' cont f a =
    applyCodeN' @b @r cont $ f >>= flip applyCode a

instance
  ( FinalType a ~ a
  , CompiledCodeFuncToHaskType (CompiledCodeIn uni fun pat a) r ~ r
  )
  => CompiledCodeFuncToHask a r uni fun pat
  where
  applyCodeN' = ($)

{-| Transform 'CompiledCode' function into a function in "Hask". This helps applying
arguments to already built script in a type safe manner. Example:
```hs
foo :: CompiledCode (Integer -> () -> Bool)
bar :: CompiledCode Integer
baz :: CompiledCode ()

applyCodeN foo bar baz :: Either String (CompiledCode Bool)
``` -}
applyCodeN
  :: forall uni fun pat a
   . CompiledCodeFuncToHask
       a
       (Either String (CompiledCodeIn uni fun pat (FinalType a)))
       uni
       fun
       pat
  => CompiledCodeIn uni fun pat a
  -> CompiledCodeFuncToHaskType
       (CompiledCodeIn uni fun pat a)
       (Either String (CompiledCodeIn uni fun pat (FinalType a)))
applyCodeN =
  applyCodeN'
    @a
    @(Either String (CompiledCodeIn uni fun pat (FinalType a)))
    id
    . pure

-- | Same as 'applyCodeN' but is partial instead of returning `Either String`.
unsafeApplyCodeN
  :: forall uni fun pat a
   . CompiledCodeFuncToHask
       a
       (CompiledCodeIn uni fun pat (FinalType a))
       uni
       fun
       pat
  => CompiledCodeIn uni fun pat a
  -> CompiledCodeFuncToHaskType
       (CompiledCodeIn uni fun pat a)
       (CompiledCodeIn uni fun pat (FinalType a))
unsafeApplyCodeN =
  applyCodeN'
    @a
    @(CompiledCodeIn uni fun pat (FinalType a))
    (either error id)
    . pure
