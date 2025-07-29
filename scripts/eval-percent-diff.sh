#!/usr/bin/env bash
# diff‑budget.sh – show percent deltas for *.eval.golden metrics
# Usage:  diff‑budget.sh [<base‑commit>]

set -euo pipefail

usage() {
  cat <<EOF
Usage: $0 [<base-commit>]

If <base-commit> is given, diff that commit against your working tree.
Otherwise, diff the working tree vs HEAD.
EOF
  exit 1
}

# --- argument parsing --------------------------------------------------------
if [[ $# -gt 1 ]]; then
  usage
elif [[ $# -eq 1 ]]; then
  BASE="$1"
  GIT_DIFF_CMD=(git diff "$BASE" -- '*.eval.golden')
else
  GIT_DIFF_CMD=(git diff -- '*.eval.golden')
fi

# --- run diff and post‑process with gawk -------------------------------------
"${GIT_DIFF_CMD[@]}" | gawk -v ESC="$(printf '\033')" '
###########################################################################
# helper functions
###########################################################################
function strip_us(num,   t){ gsub(/_/, "", num); return num+0 }         # remove underscores → number
function pct(old, new){ if (old==0) return "N/A";
                        return sprintf("%+.2f%%", 100*(new-old)/old) }  # signed Δ%
BEGIN {
  red   = ESC "[31m";      # ↑ values (worse)   → red
  green = ESC "[32m";      # ↓ values (better) → green
  reset = ESC "[0m";
}

###########################################################################
# parse diff
###########################################################################
# diff header – remember filename
/^--- a\/.*\.eval\.golden/ {
  file = substr($2, 3);          # cut leading "a/"
  print "\n" file;               # blank line between files
  next
}

# removed line (old value)
match($0, /^-([A-Za-z ]+):[[:space:]]+([0-9_]+)/, m) {
  label         = m[1]
  old[label]    = strip_us(m[2])
  old_raw[label]= m[2]           # keep original text for pretty print
  next
}

# added line (new value) – do the math & colourise
match($0, /^\+([A-Za-z ]+):[[:space:]]+([0-9_]+)/, m) {
  label   = m[1]
  new     = strip_us(m[2])
  raw_new = m[2]

  if (label in old) {            # only if we saw the matching “‑” line
    delta = pct(old[label], new)
    color = (new < old[label]) ? green : red
    printf("  %-11s %10s -> %s%10s (%s)%s\n",
           label ":", old_raw[label], color, raw_new, delta, reset)
    delete old[label]            # clear for safety
  }
}
'
