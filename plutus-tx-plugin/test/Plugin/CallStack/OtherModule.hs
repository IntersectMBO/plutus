module Plugin.CallStack.OtherModule where

import PlutusTx.Prelude

errorWhenTrue :: Bool -> BuiltinString
errorWhenTrue True  = traceError callStack
errorWhenTrue False = callStack

wraps :: Bool -> BuiltinString
wraps = errorWhenTrue

class MyClassInOtherModule a where
  myClassFuncInOtherModule :: a -> BuiltinString

instance MyClassInOtherModule Integer where
  myClassFuncInOtherModule 8 = wraps True
  myClassFuncInOtherModule _ = traceError callStack

instance MyClassInOtherModule () where
  myClassFuncInOtherModule () = traceError callStack
