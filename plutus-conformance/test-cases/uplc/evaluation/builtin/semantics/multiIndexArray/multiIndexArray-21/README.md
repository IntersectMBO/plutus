# multiIndexArray-21: String elements retain their values, order and duplicates

Array argument: `(con (array string) ["alpha", "beta"])`.

Index argument: `(con (list integer) [1, 0, 1])`.

Expected result: `(con (list string) ["beta", "alpha", "beta"])`.
