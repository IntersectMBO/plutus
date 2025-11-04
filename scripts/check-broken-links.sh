TARGETS=(
    .github/{ISSUE_TEMPLATE/*,*.md,*.yml} 
    **/{LICENSE,NOTICE,README.md,TRIAGE.md} 
    CODE_OF_CONDUCT.md 
    *.adoc
)

# For some reason linkchecker fails to check these URLs though they are valid.
# It's plausible that these domains are blocking the linkchecker user agent, or 
# that we are running into rate-limiting issues, or that linkchecker is 
# not following redirects properly.
IGNORE_URLS=(
    https://www.haskell.org/cabal
    https://pvp.haskell.org
    https://github.com/cardano-foundation/CIPs/pulls\?q\=is%3Apr+is%3Aopen+label%3A%22Category%3A+Plutus%22
    https://github.com/IntersectMBO/plutus/issues\?q\=is%3Aissue%20state%3Aopen%20label%3A%22status%3A%20needs%20triage%22
)

check_links() {
    linkchecker --no-warnings --recursion-level 0 --output failures --check-extern --stdin
}

grep_links() {
    for file in $(find "${TARGETS[@]}"); do
        grep -oE "\b(https?://|www\.)[^\[\(\)\"\ ]+\b" "${file}"
    done
}

valid_links() {
    local all_links="$(grep_links | tr ' ' '\n' | sort | uniq)"
    local ignore_links="$(echo "${IGNORE_URLS[@]}" | tr ' ' '\n' | sort | uniq)"
    comm -3 <(echo "$all_links") <(echo "$ignore_links")
}

check_links <<< "$(valid_links)"

if [[ "$?" != "0" ]]; then
    echo "Found broken links, see output above"
    exit 1
fi

