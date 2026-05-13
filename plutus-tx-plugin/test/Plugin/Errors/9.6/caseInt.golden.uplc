Error: Unsupported feature: Cannot pattern match on a value of type 'Integer'.

       This usually happens when pattern matching on an integer literal,
       for example:

         f 42 = ...
         f n  = ...

       Plinth does not support pattern matching on 'Integer'. Use equality
       from 'PlutusTx.Prelude' instead, for example:

         import PlutusTx.Prelude ((==))

         f n | n == 42   = ...
             | otherwise = ...

       Note: GHC can generate these unexpectedly, you may need '-fno-strictness', '-fno-specialise', '-fno-spec-constr', '-fno-unbox-strict-fields', or '-fno-unbox-small-strict-fields'.