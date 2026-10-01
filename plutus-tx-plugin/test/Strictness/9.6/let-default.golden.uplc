(program
   1.2.0
   (\m ->
      case (lessThanInteger m 0) [m, ((\cse -> addInteger cse cse) (error m))]))