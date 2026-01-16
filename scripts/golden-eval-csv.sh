#!/usr/bin/env bash
set -euo pipefail

OUTPUT="golden_eval_diff.csv"

# CSV header
echo "file,cpu old,mem old,ast old,flat old,cpu new,mem new,ast new,flat new" > "$OUTPUT"

# Get changed *.golden.eval files
git diff --name-only HEAD -- '*.golden.eval' | while read -r file; do
    # Skip if file was deleted
    if ! git cat-file -e "HEAD:$file" 2>/dev/null; then
        continue
    fi

    filename="$(basename "$file")"

    # Function to parse the 4 numbers from input
    parse_metrics() {
        awk -F: '
            NR<=4 {
                gsub(/[_[:space:]]/, "", $2)
                print $2
            }
        '
    }

    # Old version (from git)
    read -r cpu_old mem_old ast_old flat_old < <(
        git show "HEAD:$file" | parse_metrics | xargs echo
    )

    # New version (working tree)
    read -r cpu_new mem_new ast_new flat_new < <(
        parse_metrics < "$file" | xargs echo
    )

    # Write CSV row
    echo "$filename,$cpu_old,$mem_old,$ast_old,$flat_old,$cpu_new,$mem_new,$ast_new,$flat_new" >> "$OUTPUT"
done
