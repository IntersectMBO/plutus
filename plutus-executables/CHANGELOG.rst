
.. _changelog-1.70.0.0:

1.70.0.0 — 2026-09-22
=====================

Fixed
-----

- `uplc optimise --certify` now exits with a non-zero exit code when certification fails in the `--certifier-basic` and `--certifier-report` output modes, instead of exiting successfully. It also prints whether certification succeeded in every output mode.

.. _changelog-1.43.0.0:

1.43.0.0 — 2025-03-20
=====================

Fixed
-----

- Impossibly long certification of the Marlowe semantics example now takes ~20s
