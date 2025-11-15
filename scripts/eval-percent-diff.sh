#!/usr/bin/env bash
# diff‑budget.sh – show percent deltas for *.golden.eval metrics
# Usage:  diff‑budget.sh [-t] [<base-commit>]
#    -t    output as Markdown tables instead of colored text

set -euo pipefail

usage() {
  cat <<EOF
Usage: $0 [-t] [<base-commit>]

  -t             output as Markdown tables
  <base-commit>  if given, diff that commit against your working tree;
                 otherwise diff working tree vs HEAD.
EOF
  exit 1
}

# --- flag parsing ------------------------------------------------------------
TFLAG=0
while getopts ":t" opt; do
  case $opt in
    t) TFLAG=1 ;;
    *) usage ;;
  esac
done
shift $((OPTIND - 1))

# --- positional argument (base commit) --------------------------------------
if [[ $# -gt 1 ]]; then
  usage
elif [[ $# -eq 1 ]]; then
  BASE="$1"
  GIT_DIFF_CMD=(git diff "$BASE" -- '*.golden.eval')
else
  GIT_DIFF_CMD=(git diff -- '*.golden.eval')
fi

# --- run diff and post‑process ----------------------------------------------
if [[ $TFLAG -eq 1 ]]; then
  # Markdown table output
  "${GIT_DIFF_CMD[@]}" | gawk '
  function strip_us(num,   t) { gsub(/_/, "", num); return num+0 }
  function pct(old, new) {
    if (old==0) return "N/A";
    return sprintf("%+.2f%%", 100*(new-old)/old)
  }
  BEGIN {
    known["CPU"]=1; known["Memory"]=1;
    known["Term Size"]=1; known["Flat Size"]=1;
    file=""; seen=0;
  }
  # new file header: reset seen flag, store filename
  /^--- a\/.*\.eval\.golden/ {
    file = substr($2,3)
    seen = 0
    next
  }
  # capture old values
  /^-[A-Za-z ]+:[[:space:]]+[0-9_]+/ {
    match($0,/^-([A-Za-z ]+):[[:space:]]+([0-9_]+)/,m)
    label=m[1]; if (!(label in known)) next
    old[label]=strip_us(m[2]); old_raw[label]=m[2]
    next
  }
  # capture new values and print row (with header if first)
  /^\+[A-Za-z ]+:[[:space:]]+[0-9_]+/ {
    match($0,/^\+([A-Za-z ]+):[[:space:]]+([0-9_]+)/,m)
    label=m[1]; if (!(label in known)) next
    newval=strip_us(m[2]); raw_new=m[2]
    if (label in old) {
      delta=pct(old[label],newval)
      if (!seen) {
        print ""
        print "### " file
        print ""
        print "| Metric     | Old     | New     | Δ%      |"
        print "|------------|---------|---------|---------|"
        seen=1
      }
      printf("| %-10s | `%7s` | `%7s` | %7s |\n",
             label, old_raw[label], raw_new, delta)
      delete old[label]
    }
  }
  '
else
  # Colored text output
  "${GIT_DIFF_CMD[@]}" | gawk -v ESC="$(printf '\033')" '
  function strip_us(num,   t) { gsub(/_/, "", num); return num+0 }
  function pct(old, new) {
    if (old==0) return "N/A";
    return sprintf("%+.2f%%", 100*(new-old)/old)
  }
  BEGIN {
    known["CPU"]=1; known["Memory"]=1;
    known["Term Size"]=1; known["Flat Size"]=1;
    red   = ESC "[31m"; green = ESC "[32m"; reset = ESC "[0m";
    file=""; seen=0;
  }
  # new file header: reset seen flag, store filename
  /^--- a\/.*\.eval\.golden/ {
    file = substr($2,3)
    seen = 0
    next
  }
  # capture old values
  /^-[A-Za-z ]+:[[:space:]]+[0-9_]+/ {
    match($0,/^-([A-Za-z ]+):[[:space:]]+([0-9_]+)/,m)
    label=m[1]; if (!(label in known)) next
    old[label]=strip_us(m[2]); old_raw[label]=m[2]
    next
  }
  # capture new values and print line (with filename if first)
  /^\+[A-Za-z ]+:[[:space:]]+[0-9_]+/ {
    match($0,/^\+([A-Za-z ]+):[[:space:]]+([0-9_]+)/,m)
    label=m[1]; if (!(label in known)) next
    newval=strip_us(m[2]); raw_new=m[2]
    if (label in old) {
      delta=pct(old[label],newval)
      color=(newval<old[label]? green: red)
      if (!seen) {
        print "\n" file
        seen=1
      }
      printf("  %-11s %10s -> %s%10s (%s)%s\n",
             label ":", old_raw[label], color, raw_new, delta, reset)
      delete old[label]
    }
  }
  '
fi
