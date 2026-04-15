(program
   1.1.0
   (\items ->
      case
        (case items [(\ds ds -> constr 0 [ds]), (constr 1 [])])
        [ (\ds ->
             (\wild -> ())
               (case items [(\ds ds -> constr 0 [ds]), (constr 1 [])]))
        , ((\wild -> ())
             (case items [(\ds ds -> constr 0 [ds]), (constr 1 [])])) ]))