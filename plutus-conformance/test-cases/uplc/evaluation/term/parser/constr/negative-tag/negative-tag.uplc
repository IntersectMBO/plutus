-- Negative tags are not allowed
-- This program isn't representable in flat because it uses an unsigned Word64 for the tag.
(program 1.1.0
    (constr -5 (con integer 1) (error))
)
