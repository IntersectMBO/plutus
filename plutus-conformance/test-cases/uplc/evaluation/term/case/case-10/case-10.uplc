-- This should not fail: a case expression with an empty list of branches is
-- legal (but attempting to use it to branch on any `constr` term will cause an
-- error).
(program 1.1.0
  (lam x (case x))
)
