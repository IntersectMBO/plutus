let
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  ~fail :
     unit -> Maybe bool
    = \(ds : unit) ->
        trace
          {all dead a. Maybe a}
          "CoverLocation (CovLoc {_covLocFile = \"test/Plugin/Coverage/Spec.hs\", _covLocStartLine = 40, _covLocEndLine = 40, _covLocStartCol = 14, _covLocEndCol = 15})"
          (/\dead ->
             trace
               {all dead a. Maybe a}
               "CoverLocation (CovLoc {_covLocFile = \"test/Plugin/Coverage/Spec.hs\", _covLocStartLine = 42, _covLocEndLine = 42, _covLocStartCol = 8, _covLocEndCol = 15})"
               (/\dead -> Nothing)
               {all dead. dead})
          {all dead. dead}
          {bool}
  !equalsInteger : integer -> integer -> bool = equalsInteger
  ~equalsInteger : integer -> integer -> bool
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in equalsInteger x y
  ~`$fEqInteger` : (\a -> a -> a -> bool) integer = equalsInteger
  ~`&&` : bool -> bool -> bool
    = \(ds : bool) (x : bool) ->
        case (all dead. bool) ds [(/\dead -> False), (/\dead -> x)]
          {all dead. dead}
  ~`==` : all a. (\a -> a -> a -> bool) a -> a -> a -> bool
    = /\a -> \(v : (\a -> a -> a -> bool) a) -> v
  !trace : all a. string -> a -> a = trace
  ~traceBool : string -> string -> bool -> bool
    = \(trueLabel : string) ->
        let
          !trueLabel : string = trueLabel
        in
        \(falseLabel : string) ->
          let
            !falseLabel : string = falseLabel
          in
          \(c : bool) ->
            case
              (all dead. bool)
              c
              [ (/\dead -> trace {bool} falseLabel False)
              , (/\dead -> trace {bool} trueLabel True) ]
              {all dead. dead}
  ~otherFun :
     integer -> bool
    = \(x : integer) ->
        let
          !x : integer = x
        in
        traceBool
          "CoverBool (CovLoc {_covLocFile = \"test/Plugin/Coverage/Spec.hs\", _covLocStartLine = 46, _covLocEndLine = 46, _covLocStartCol = 1, _covLocEndCol = 32}) True"
          "CoverBool (CovLoc {_covLocFile = \"test/Plugin/Coverage/Spec.hs\", _covLocStartLine = 46, _covLocEndLine = 46, _covLocStartCol = 1, _covLocEndCol = 32}) False"
          (trace
             {all dead. bool}
             "CoverLocation (CovLoc {_covLocFile = \"test/Plugin/Coverage/Spec.hs\", _covLocStartLine = 46, _covLocEndLine = 46, _covLocStartCol = 1, _covLocEndCol = 32})"
             (/\dead ->
                traceBool
                  "CoverBool (CovLoc {_covLocFile = \"test/Plugin/Coverage/Spec.hs\", _covLocStartLine = 46, _covLocEndLine = 46, _covLocStartCol = 14, _covLocEndCol = 32}) True"
                  "CoverBool (CovLoc {_covLocFile = \"test/Plugin/Coverage/Spec.hs\", _covLocStartLine = 46, _covLocEndLine = 46, _covLocStartCol = 14, _covLocEndCol = 32}) False"
                  (trace
                     {all dead. bool}
                     "CoverLocation (CovLoc {_covLocFile = \"test/Plugin/Coverage/Spec.hs\", _covLocStartLine = 46, _covLocEndLine = 46, _covLocStartCol = 14, _covLocEndCol = 32})"
                     (/\dead ->
                        `&&`
                          (traceBool
                             "CoverBool (CovLoc {_covLocFile = \"test/Plugin/Coverage/Spec.hs\", _covLocStartLine = 46, _covLocEndLine = 46, _covLocStartCol = 14, _covLocEndCol = 24}) True"
                             "CoverBool (CovLoc {_covLocFile = \"test/Plugin/Coverage/Spec.hs\", _covLocStartLine = 46, _covLocEndLine = 46, _covLocStartCol = 14, _covLocEndCol = 24}) False"
                             (trace
                                {all dead. bool}
                                "CoverLocation (CovLoc {_covLocFile = \"test/Plugin/Coverage/Spec.hs\", _covLocStartLine = 46, _covLocEndLine = 46, _covLocStartCol = 14, _covLocEndCol = 24})"
                                (/\dead ->
                                   `==`
                                     {integer}
                                     `$fEqInteger`
                                     (trace
                                        {all dead. integer}
                                        "CoverLocation (CovLoc {_covLocFile = \"test/Plugin/Coverage/Spec.hs\", _covLocStartLine = 46, _covLocEndLine = 46, _covLocStartCol = 15, _covLocEndCol = 16})"
                                        (/\dead -> x)
                                        {all dead. dead})
                                     (trace
                                        {all dead. integer}
                                        "CoverLocation (CovLoc {_covLocFile = \"test/Plugin/Coverage/Spec.hs\", _covLocStartLine = 46, _covLocEndLine = 46, _covLocStartCol = 22, _covLocEndCol = 23})"
                                        (/\dead -> 5)
                                        {all dead. dead}))
                                {all dead. dead}))
                          (trace
                             {all dead. bool}
                             "CoverLocation (CovLoc {_covLocFile = \"test/Plugin/Coverage/Spec.hs\", _covLocStartLine = 46, _covLocEndLine = 46, _covLocStartCol = 28, _covLocEndCol = 32})"
                             (/\dead -> True)
                             {all dead. dead}))
                     {all dead. dead}))
             {all dead. dead})
in
\(x : Maybe integer) ->
  let
    !x : Maybe integer = x
  in
  trace
    {all dead. Maybe bool}
    "CoverLocation (CovLoc {_covLocFile = \"test/Plugin/Coverage/Spec.hs\", _covLocStartLine = 37, _covLocEndLine = 37, _covLocStartCol = 54, _covLocEndCol = 57})"
    (/\dead ->
       trace
         {all dead. Maybe bool}
         "CoverLocation (CovLoc {_covLocFile = \"test/Plugin/Coverage/Spec.hs\", _covLocStartLine = 40, _covLocEndLine = 42, _covLocStartCol = 1, _covLocEndCol = 15})"
         (/\dead ->
            trace
              {all dead. Maybe bool}
              "CoverLocation (CovLoc {_covLocFile = \"test/Plugin/Coverage/Spec.hs\", _covLocStartLine = 40, _covLocEndLine = 42, _covLocStartCol = 9, _covLocEndCol = 15})"
              (/\dead ->
                 Maybe_match
                   {integer}
                   x
                   {all dead. Maybe bool}
                   (\(y : integer) ->
                      /\dead ->
                        trace
                          {all dead. Maybe bool}
                          "CoverLocation (CovLoc {_covLocFile = \"test/Plugin/Coverage/Spec.hs\", _covLocStartLine = 41, _covLocEndLine = 41, _covLocStartCol = 12, _covLocEndCol = 22})"
                          (/\dead ->
                             case
                               (all dead. Maybe bool)
                               (otherFun
                                  (trace
                                     {all dead. integer}
                                     "CoverLocation (CovLoc {_covLocFile = \"test/Plugin/Coverage/Spec.hs\", _covLocStartLine = 41, _covLocEndLine = 41, _covLocStartCol = 21, _covLocEndCol = 22})"
                                     (/\dead -> y)
                                     {all dead. dead}))
                               [ (/\dead -> fail ())
                               , (/\dead ->
                                    trace
                                      {all dead. Maybe bool}
                                      "CoverLocation (CovLoc {_covLocFile = \"test/Plugin/Coverage/Spec.hs\", _covLocStartLine = 41, _covLocEndLine = 41, _covLocStartCol = 26, _covLocEndCol = 36})"
                                      (/\dead ->
                                         Just
                                           {bool}
                                           (trace
                                              {all dead. bool}
                                              "CoverLocation (CovLoc {_covLocFile = \"test/Plugin/Coverage/Spec.hs\", _covLocStartLine = 41, _covLocEndLine = 41, _covLocStartCol = 31, _covLocEndCol = 36})"
                                              (/\dead -> False)
                                              {all dead. dead}))
                                      {all dead. dead}) ]
                               {all dead. dead})
                          {all dead. dead})
                   (/\dead -> fail ())
                   {all dead. dead})
              {all dead. dead})
         {all dead. dead})
    {all dead. dead}