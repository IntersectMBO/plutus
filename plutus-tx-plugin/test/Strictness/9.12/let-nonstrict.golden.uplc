(program
   1.1.0
   (\m ->
      case (lessThanInteger m 0) [m, ((\cse -> addInteger cse cse) (error m))]))