-- It's legal to have a case term with no branches,
-- but applying it causes an error.
(program 1.1.0
    (case (constr 0))
)
