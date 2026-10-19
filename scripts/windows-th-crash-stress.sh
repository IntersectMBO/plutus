#!/usr/bin/env bash

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

HN_REF="github:input-output-hk/haskell.nix/d93d6ed0f367d732b146666cee65cded175c6160"
# Pin haskell.nix's nested nixpkgs to the project's locked rev (flake.lock,
# nixpkgs-unstable). Without this the haskell-nix override also swaps in a
# newer nixpkgs whose Wine hangs during headless prefix init; pinning it keeps
# Wine identical across all arms, so only the GHC toolchain varies.
NIXPKGS_REF="github:NixOS/nixpkgs/a683adc19ff5228af548c6539dbc3440509bfed3"
HN_OVERRIDE="--override-input haskell-nix $HN_REF --override-input haskell-nix/nixpkgs-unstable $NIXPKGS_REF"

declare -A GHC_VARIANT=(
  [ghc96]="ghc96"
  [ghc912]="ghc912"
  [ghc9123]="ghc9123"
)
declare -A GHC_OVERRIDE=(
  [ghc96]=""
  [ghc912]=""
  [ghc9123]="$HN_OVERRIDE"
)
variant_for() { echo "${GHC_VARIANT[$1]:-$1}"; }
override_for() {
  if [ -n "${GHC_OVERRIDE[$1]+set}" ]; then echo "${GHC_OVERRIDE[$1]}";
  else echo "$HN_OVERRIDE"; fi
}

GHCS=(ghc96 ghc912 ghc9123)
MAX_ITERS=0
MAX_HOURS=0
MAX_SILENT=3600
RESULTS_DIR="$REPO_ROOT/windows-th-crash-stress-results"
SYSTEM=""
EXTRA_NIX_ARGS=()

usage() {
  cat <<EOF
Usage: scripts/windows-th-crash-stress.sh [-g "ghc96 ghc912 ghc9123"] [-n N]
                                          [-H HOURS] [-d RESULTS_DIR] [-s SYSTEM]
                                          [-- <extra nix args>]

  -g "A B ..."  Space-separated build arms. Default: "ghc96 ghc912 ghc9123".
  -n N          Stop after N iterations PER arm (0 = unlimited). Default: 0.
  -H HOURS      Stop after ~HOURS hours (fractional ok, 0 = no limit). Default: 0.
  -t SECONDS    Kill a build after SECONDS with no output (hung Wine guard,
                0 = disabled). Default: 3600.
  -d DIR        Results directory. Default: <repo>/windows-th-crash-stress-results
  -s SYSTEM     Nix system. Default: autodetected (e.g. x86_64-linux).
  --            Everything after is passed verbatim to 'nix build'.

Stop with Ctrl-C or:  touch <DIR>/STOP
EOF
}

while getopts ":g:n:H:t:d:s:h" opt; do
  case "$opt" in
    g) read -r -a GHCS <<< "$OPTARG" ;;
    n) MAX_ITERS="$OPTARG" ;;
    H) MAX_HOURS="$OPTARG" ;;
    t) MAX_SILENT="$OPTARG" ;;
    d) RESULTS_DIR="$OPTARG" ;;
    s) SYSTEM="$OPTARG" ;;
    h) usage; exit 0 ;;
    \?) echo "Unknown option: -$OPTARG" >&2; exit 2 ;;
    :)  echo "Option -$OPTARG requires an argument" >&2; exit 2 ;;
  esac
done
shift $((OPTIND - 1))
EXTRA_NIX_ARGS=("$@")

command -v nix >/dev/null 2>&1 || { echo "ERROR: 'nix' not found on PATH." >&2; exit 1; }
SYSTEM="${SYSTEM:-$(nix eval --impure --raw --expr 'builtins.currentSystem' 2>/dev/null || echo x86_64-linux)}"

attr_for() {
  echo ".#__internal.${SYSTEM}.project.projectVariants.$(variant_for "$1").projectCross.mingwW64.hsPkgs.plutus-core.components.library"
}

TARGET_RE='scavenge_stack: weird activation record found on stack'
ISERV_RE='ghc-iserv terminated|iserv-proxy[^[:space:]]*: internal error|iserv-proxy.*end of file|GHCi\.Message\.remoteCall: end of file|remote-iserv|wine.*Unhandled exception'
NONDET_RE='may not be deterministic|is not deterministic|not deterministic!'
CHECKIMPOSSIBLE_RE='are not valid, so checking is not possible'
EVALFAIL_RE='error: .*attribute .* (missing|not found)|Did you mean|does not provide attribute|cannot find flake'

mkdir -p "$RESULTS_DIR/logs"
CSV="$RESULTS_DIR/results.csv"
SUMMARY="$RESULTS_DIR/summary.txt"
[ -f "$CSV" ] || echo "timestamp,arm,attempt,class,rc,duration_s,logfile" > "$CSV"

declare -A ATTEMPTS TARGET ISERV OTHERFAIL SUCCESS
for g in "${GHCS[@]}"; do ATTEMPTS[$g]=0; TARGET[$g]=0; ISERV[$g]=0; OTHERFAIL[$g]=0; SUCCESS[$g]=0; done
START_EPOCH=$(date +%s)

print_summary() {
  {
    echo "==== Windows TH crash stress summary ===="
    echo "system : $SYSTEM"
    echo "started: $(date -d "@$START_EPOCH" '+%F %T' 2>/dev/null || echo "@$START_EPOCH")"
    echo "now    : $(date '+%F %T')"
    echo "target : scavenge_stack: weird activation record found on stack"
    echo
    printf "%-14s %9s %13s %12s %11s %9s %8s\n" \
      ARM attempts TARGET_CRASH iserv_other other_fail success "crash%"
    for g in "${GHCS[@]}"; do
      local a=${ATTEMPTS[$g]} tc=${TARGET[$g]} rate
      rate=$(awk -v a="$a" -v c="$tc" 'BEGIN{ if(a>0) printf "%.1f", 100*c/a; else printf "n/a" }')
      printf "%-14s %9d %13d %12d %11d %9d %7s%%\n" \
        "$g" "$a" "$tc" "${ISERV[$g]}" "${OTHERFAIL[$g]}" "${SUCCESS[$g]}" "$rate"
    done
    echo
    echo "tally     : $CSV"
    echo "crash logs: $RESULTS_DIR/logs/  (only crashes/failures kept)"
  } > "$SUMMARY"
  cat "$SUMMARY"
}

finish() { echo; echo ">>> stopping; final summary:"; print_summary; exit 0; }
trap finish INT TERM

time_up() {
  [ "$MAX_HOURS" = 0 ] && return 1
  awk -v s="$START_EPOCH" -v now="$(date +%s)" -v h="$MAX_HOURS" 'BEGIN{ exit !((now-s)/3600 >= h) }'
}

run_build() {
  local g="$1" log="$2" rc
  local attr; attr=$(attr_for "$g")
  local ovarr; read -r -a ovarr <<< "$(override_for "$g")"
  local silentarr=()
  [ "$MAX_SILENT" != 0 ] && silentarr=(--max-silent-time "$MAX_SILENT")
  nix build "$attr" --rebuild --no-link --print-build-logs \
    "${silentarr[@]}" "${ovarr[@]}" "${EXTRA_NIX_ARGS[@]}" > "$log" 2>&1
  rc=$?
  if [ "$rc" -ne 0 ] && grep -q "$CHECKIMPOSSIBLE_RE" "$log"; then
    nix build "$attr" --no-link --print-build-logs \
      "${silentarr[@]}" "${ovarr[@]}" "${EXTRA_NIX_ARGS[@]}" > "$log" 2>&1
    rc=$?
  fi
  echo "$rc"
}

for g in "${GHCS[@]}"; do
  attr=$(attr_for "$g")
  read -r -a ovarr <<< "$(override_for "$g")"
  echo "[preflight] $g -> evaluating (variant $(variant_for "$g")${ovarr[*]:+, ${ovarr[*]}}) ..."
  if ! nix eval --raw "${attr}.drvPath" "${ovarr[@]}" >/dev/null 2>"$RESULTS_DIR/preflight-${g}.err"; then
    echo "ERROR: failed to evaluate $g" >&2
    echo "  attr: $attr" >&2
    [ "${#ovarr[@]}" -gt 0 ] && echo "  override: ${ovarr[*]}" >&2
    echo "  * For ghc9123: is the inert variant present in nix/project.nix" >&2
    echo "    (flake.variants.ghc9123.compiler-nix-name = \"ghc9123\")?" >&2
    echo "  * See $RESULTS_DIR/preflight-${g}.err" >&2
    exit 1
  fi
done
echo "[preflight] ok: ${GHCS[*]}  (system: $SYSTEM)"
echo

while true; do
  [ -e "$RESULTS_DIR/STOP" ] && { echo "STOP file present."; break; }
  all_done=1
  for g in "${GHCS[@]}"; do
    if [ "$MAX_ITERS" != 0 ] && [ "${ATTEMPTS[$g]}" -ge "$MAX_ITERS" ]; then continue; fi
    all_done=0
    n=$(( ATTEMPTS[$g] + 1 ))
    ts=$(date +%Y%m%dT%H%M%S)
    log="$RESULTS_DIR/logs/${g}-$(printf '%04d' "$n")-${ts}.log"

    echo "[$(date '+%F %T')] $g #$n  building ..."
    t0=$(date +%s)
    rc=$(run_build "$g" "$log")
    dur=$(( $(date +%s) - t0 ))
    ATTEMPTS[$g]=$n

    if [ "$rc" -ne 0 ] && grep -qE "$EVALFAIL_RE" "$log"; then
      echo "  -> EVAL_FAIL: flake attribute for arm '$g' did not evaluate; this is" >&2
      echo "     deterministic (wrong checkout or missing haskell-nix override), aborting." >&2
      echo "     See $log" >&2
      echo "${ts},${g},${n},EVAL_FAIL,${rc},${dur},${log}" >> "$CSV"
      print_summary
      exit 1
    fi
    if grep -qE "$TARGET_RE" "$log"; then
      class=TARGET_CRASH;      TARGET[$g]=$(( TARGET[$g] + 1 ))
    elif grep -qE "$ISERV_RE" "$log"; then
      class=ISERV_CRASH_OTHER; ISERV[$g]=$(( ISERV[$g] + 1 ))
    elif grep -qE "$NONDET_RE" "$log"; then
      class=SUCCESS_NONDET;    SUCCESS[$g]=$(( SUCCESS[$g] + 1 ))
    elif [ "$rc" -ne 0 ]; then
      class=BUILD_FAIL_OTHER;  OTHERFAIL[$g]=$(( OTHERFAIL[$g] + 1 ))
    else
      class=SUCCESS;           SUCCESS[$g]=$(( SUCCESS[$g] + 1 ))
    fi

    echo "  -> $class  (rc=$rc, ${dur}s)"
    echo "${ts},${g},${n},${class},${rc},${dur},${log}" >> "$CSV"
    case "$class" in
      TARGET_CRASH|ISERV_CRASH_OTHER|BUILD_FAIL_OTHER) : ;;
      *) rm -f "$log" ;;
    esac
    print_summary >/dev/null

    [ -e "$RESULTS_DIR/STOP" ] && { echo "STOP file present."; finish; }
    time_up && { echo "Time limit reached."; finish; }
  done
  if [ "$all_done" = 1 ]; then echo "All arms reached MAX_ITERS=$MAX_ITERS."; break; fi
done

print_summary
