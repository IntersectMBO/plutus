(program
   1.1.0
   (\bd bd ->
      case
        (constr 0 [#, #, (unionValue (unValueData bd) (unValueData bd))])
        [lookupCoin]))