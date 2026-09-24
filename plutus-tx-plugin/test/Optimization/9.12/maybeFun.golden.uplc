program
  1.2.0
  (\ds ds ->
     case
       ds
       [ (\x' ->
            case ds [(\y' -> constr 0 [(addInteger x' y')]), (constr 1 [])])
       , (constr 1 []) ])