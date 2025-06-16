-- It's legal to have a case term with no branches, but using it to branch on
-- any `constr` term will cause an error, so this will fail.
(program 1.1.0
    (case (constr 0))
)
