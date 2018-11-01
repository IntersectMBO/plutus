#!/usr/bin/env bash

set -euo pipefail

# Name of the programm to run
EXE="$1"

# The other arguments are passed to it
shift

# The verbosy flag is needed because the tests don't run with an utf8-aware
# locale, and this causes a crash in criterion because of of
# https://github.com/bos/criterion/issues/205
exec "$EXE" \
    "--csv=$TEST_UNDECLARED_OUTPUTS_DIR/result.csv" \
    "--json=$TEST_UNDECLARED_OUTPUTS_DIR/result.json" \
    "--output=$TEST_UNDECLARED_OUTPUTS_DIR/result.html" \
    "--junit=$TEST_UNDECLARED_OUTPUTS_DIR/result.xml" \
    "--verbosity=0" \
    "$@"