# dropPolicies-24: Filter a large Value

Filter a stress input with 200 policies and 200 token names per policy. Request #00c7, #0000, #0063, #0000 and absent #ffff in that order. Observe policies of the result to distinguish the remaining set from the selected set and catch an incorrect policy selection.

Expected result: the 197 policy IDs #0001 through #00c6, excluding #0063, in ascending byte order.
