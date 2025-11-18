{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}

module CallTrace.OtherModule where

import PlutusTx.Prelude

errorWhenTrue :: Bool -> BuiltinString
errorWhenTrue True = error ()
errorWhenTrue False = "hi"

wraps :: Bool -> BuiltinString
wraps = errorWhenTrue

class MyClassInOtherModule a where
  myClassFuncInOtherModule :: a -> BuiltinString

instance MyClassInOtherModule Integer where
  myClassFuncInOtherModule 8 = wraps True
  myClassFuncInOtherModule _ = error ()

instance MyClassInOtherModule () where
  myClassFuncInOtherModule () = error ()
