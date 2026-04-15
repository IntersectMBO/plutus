Error: Unsupported feature: Variable validator
       OtherCon []

       This error often indicates a stage violation in Plinth compilation.
       Variables inside compile quotations must be either:
         • Top-level variables, or
         • Bound inside the quotation itself

       Common causes:
         • Using a function defined in a 'where' clause: move it to the top level
         • Referencing local variables from outside the quotation