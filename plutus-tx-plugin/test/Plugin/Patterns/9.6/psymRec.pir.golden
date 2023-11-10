let
  data (Example :: * -> *) a | Example_match where
    EInt : integer -> Example a
    ETwo : a -> a -> Example a
  ~`$WETwo` : all a. a -> a -> Example a
    = /\a ->
        \(conrep : a) ->
          let
            !conrep : a = conrep
          in
          \(conrep : a) -> let !conrep : a = conrep in ETwo {a} conrep conrep
  ~`$bERec` : all a. a -> a -> Example a
    = /\a ->
        \(hello : a) ->
          let
            !hello : a = hello
          in
          \(world : a) -> let !world : a = world in `$WETwo` {a} hello world
  ~`$mERec` : all r a. Example a -> (a -> a -> r) -> (unit -> r) -> r
    = /\r a ->
        \(scrut : Example a) ->
          let
            !scrut : Example a = scrut
          in
          \(cont : a -> a -> r) ->
            let
              !cont : a -> a -> r = cont
            in
            \(fail : unit -> r) ->
              let
                !fail : unit -> r = fail
              in
              Example_match
                {a}
                scrut
                {r}
                (\(ipv : integer) -> fail ())
                (\(hello : a) (world : a) -> cont hello world)
  !r : Example string = `$bERec` {string} "wot" "yo"
in
`$mERec`
  {string}
  {string}
  r
  (\(ds : string) (ds : string) -> ds)
  (\(void : unit) -> "no")