-- Captures are applied depth-first and left-to-right through a pair and nested list.
(program 1.2.0
  (match (con (pair integer (list bytestring)) (7, [#aa, #bb]))
    (pattern
      (pair (bind) (list (wildcard) (bind)))
      (lam left (lam right (constr 0 left right))))
    (pattern (wildcard) (error)))
)
