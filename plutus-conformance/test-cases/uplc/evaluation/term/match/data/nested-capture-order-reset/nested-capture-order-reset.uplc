-- Exercise nested Data.List/Map/Pair/I/B matching. The first alternative captures twice and then
-- fails on map width; the chosen alternative must start with a fresh capture sequence.
(program 1.2.0
  (match
    (con data
      (Constr 9
        [ List [I 11, I 22]
        , Map [(I 1, B #aa)]
        , B #bb
        ]))
    (pattern
      (data-constr 9
        (data-list (data-i (bind)) (bind))
        (data-map)
        (wildcard))
      (lam abandoned1 (lam abandoned2 (error))))
    (pattern
      (data-constr 9
        (data-list (data-i (bind)) (bind))
        (data-map
          (pair
            (data-i (integer 1))
            (data-b (bind))))
        (data-b (bind)))
      (lam first
        (lam second
          (lam third
            (lam fourth
              (constr 0 first second third fourth))))))
    (pattern (wildcard) (error)))
)
