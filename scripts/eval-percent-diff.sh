#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<EOF
Usage: $0 [<base-commit>]

If <base-commit> is provided, diffs that commit against your working tree.
Otherwise diffs your working tree vs HEAD.
EOF
  exit 1
}

# parse optional commit
if [[ $# -gt 1 ]]; then
  usage
elif [[ $# -eq 1 ]]; then
  BASE="$1"
  GIT_DIFF_CMD=(git diff "$BASE" -- '*.eval.golden')
else
  GIT_DIFF_CMD=(git diff -- '*.eval.golden')
fi

# run diff and compute percentages with color & alignment
"${GIT_DIFF_CMD[@]}" | awk '
BEGIN {
  esc   = sprintf("%c", 27)
  red   = esc "[31m"
  green = esc "[32m"
  reset = esc "[0m"
}

# capture filename
/^--- a\/.*\.eval\.golden/ {
  file = substr($2, 3)
}

# old values (strip underscores)
/^-CPU:/       { oldCPU  = $2; gsub(/[_]/, "", oldCPU) }
/^-Memory:/    { oldMem  = $2; gsub(/[_]/, "", oldMem) }
/^-Term Size:/ { oldTerm = $3 }
/^-Flat Size:/ { oldFlat = $3 }

# new values + print on Flat Size
/^\+CPU:/        { newCPU  = $2; gsub(/[_]/, "", newCPU) }
/^\+Memory:/     { newMem  = $2; gsub(/[_]/, "", newMem) }
/^\+Term Size:/  { newTerm = $3 }
/^\+Flat Size:/ {
  newFlat = $3

  print "File:", file

  # CPU
  if (oldCPU && newCPU) {
    pct   = (newCPU - oldCPU) / oldCPU * 100
    color = (pct < 0 ? green : (pct > 0 ? red : reset))
    printf("  %-11s%s%+7.2f%%%s\n", "CPU:", color, pct, reset)
  }

  # Memory
  if (oldMem && newMem) {
    pct   = (newMem - oldMem) / oldMem * 100
    color = (pct < 0 ? green : (pct > 0 ? red : reset))
    printf("  %-11s%s%+7.2f%%%s\n", "Memory:", color, pct, reset)
  }

  # Term Size
  if (oldTerm && newTerm) {
    pct   = (newTerm - oldTerm) / oldTerm * 100
    color = (pct < 0 ? green : (pct > 0 ? red : reset))
    printf("  %-11s%s%+7.2f%%%s\n", "Term Size:", color, pct, reset)
  }

  # Flat Size
  if (oldFlat && newFlat) {
    pct   = (newFlat - oldFlat) / oldFlat * 100
    color = (pct < 0 ? green : (pct > 0 ? red : reset))
    printf("  %-11s%s%+7.2f%%%s\n", "Flat Size:", color, pct, reset)
  }

  print ""

  # clear for next hunk
  oldCPU=newCPU=oldMem=newMem=oldTerm=newTerm=oldFlat=newFlat=""
}
'
