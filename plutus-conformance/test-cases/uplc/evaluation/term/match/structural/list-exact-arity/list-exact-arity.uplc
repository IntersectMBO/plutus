-- Exact list patterns reject both fewer and more children. Captures from failed alternatives reset.
(program 1.2.0
  (match (con (list integer) [1, 2, 3])
    (pattern (list (bind) (wildcard)) (lam abandoned (error)))
    (pattern
      (list (bind) (wildcard) (wildcard) (wildcard))
      (lam abandoned (error)))
    (pattern
      (list (wildcard) (bind) (wildcard))
      (lam middle middle))
    (pattern (wildcard) (error)))
)
