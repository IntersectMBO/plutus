# `beam-sqlite`: Beam backend for the SQLite embedded database

`beam-sqlite` is a beam backend for
the [SQLite embedded database](https://sqlite.org/). 

SQLite is mostly standards compliant, but there are a few cases that beam-sqlite
cannot handle. These cases may result in run-time errors. For more information,
see
[the documentation](https://haskell-beam.github.io/beam/user-guide/backends/beam-sqlite/).
Due to SQLite's embedded nature, there are currently no plans to get rid of
these. However, proposals and PRs to fix these corner cases are welcome, where
appropriate.
