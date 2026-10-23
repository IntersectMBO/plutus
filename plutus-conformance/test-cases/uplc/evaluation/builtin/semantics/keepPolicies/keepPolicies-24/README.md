# keepPolicies-24: Filter a large Value

Filter a stress input with 200 policies and 200 token names per policy. Request #00c7, #0000, #0063, #0000 and absent #ffff in that order. Return the selected Value to verify its policies, token names and quantities, including duplicate and absent-ID behavior.

Expected result: policies #0000, #0063 and #00c7, each with token names #0000 through #00c7 and quantity 1 (600 assets in total).
