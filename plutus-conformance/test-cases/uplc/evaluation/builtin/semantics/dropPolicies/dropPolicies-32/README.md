# dropPolicies-32: Negative quantities remain after filtering

Use the same Value and valueContains operand as the preceding case, changing only the policy list so a negative amount remains. valueContains must fail because its first argument still contains a negative quantity.

Expected result: `evaluation failure`.
