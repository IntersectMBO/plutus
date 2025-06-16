-- This should not fail: a case expression with an empty list of branches is
-- legal (but applying it to anything will cause an error).
(program 1.1.0
  (lam x (case x))
)
