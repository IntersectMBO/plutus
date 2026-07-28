(program
   1.1.0
   ((\forced
      d ->
       case
         (unConstrData d)
         [ (\idx
             args ->
              case
                idx
                [ (case args [(\hd tl -> case tl [(\hd tl -> unIData hd)])])
                , (case
                     args
                     [ (\hd
                         tl ->
                          case
                            tl
                            [ (\hd
                                tl ->
                                 case
                                   tl
                                   [ (\hd
                                       tl ->
                                        case
                                          tl
                                          [ (\hd
                                              tl ->
                                               case
                                                 tl
                                                 [ (\hd
                                                     tl ->
                                                      case
                                                        tl
                                                        [ (\hd
                                                            tl ->
                                                             addInteger
                                                               (unIData hd)
                                                               (unIData
                                                                  (forced
                                                                     tl))) ]) ]) ]) ]) ]) ])
                , (case
                     args
                     [ (\hd
                         tl ->
                          case
                            tl
                            [ (\hd
                                tl ->
                                 case
                                   tl
                                   [ (\hd
                                       tl ->
                                        case
                                          tl
                                          [ (\hd
                                              tl ->
                                               case
                                                 tl
                                                 [ (\hd
                                                     tl ->
                                                      case
                                                        tl
                                                        [ (\hd
                                                            tl ->
                                                             case
                                                               tl
                                                               [ (\hd
                                                                   tl ->
                                                                    case
                                                                      tl
                                                                      [ (\hd
                                                                          tl ->
                                                                           case
                                                                             tl
                                                                             [ (\hd
                                                                                 tl ->
                                                                                  case
                                                                                    tl
                                                                                    [ (\hd
                                                                                        tl ->
                                                                                         case
                                                                                           tl
                                                                                           [ (\hd
                                                                                               tl ->
                                                                                                case
                                                                                                  tl
                                                                                                  [ (\hd
                                                                                                      tl ->
                                                                                                       case
                                                                                                         tl
                                                                                                         [ (\hd
                                                                                                             tl ->
                                                                                                              case
                                                                                                                tl
                                                                                                                [ (\hd
                                                                                                                    tl ->
                                                                                                                     addInteger
                                                                                                                       (unIData
                                                                                                                          hd)
                                                                                                                       (addInteger
                                                                                                                          (unIData
                                                                                                                             hd)
                                                                                                                          (unIData
                                                                                                                             hd))) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ])
      (force headList)))