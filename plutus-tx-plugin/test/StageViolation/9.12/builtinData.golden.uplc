Error: Unsupported feature: Cannot construct a value of type: PlutusTx.Builtins.Internal.BuiltinData

       This error often indicates a stage violation in Plinth compilation.
       Variables inside compile quotations must be either:
         • Top-level variables, or
         • Bound inside the quotation itself

       Common causes:
         • Using a function defined in a 'where' clause: move it to the top level
         • Referencing local variables from outside the quotation

       Note: GHC can generate these unexpectedly, you may need '-fno-strictness', '-fno-specialise', '-fno-spec-constr', '-fno-unbox-strict-fields', or '-fno-unbox-small-strict-fields'.