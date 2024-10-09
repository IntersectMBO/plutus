TARGETS=(
    .github/{ISSUE_TEMPLATE/*,*.md,*.yml} 
    **/{LICENSE,NOTICE,README.md,TRIAGE.md} 
    CODE_OF_CONDUCT.md 
    *.adoc
    CONTRIBUTING.adoc
)

# For some reason linkchecker fails to check these URLs though they are valid.
# It's plausible that these domains are blocking the linkchecker user agent, or 
# that we are running into rate-limiting issues.
IGNORE_URLS=(
    https://pvp.haskell.org
    https://www.haskell.org/cabal
)

FAILED=0

check_links() {
    linkchecker --no-warnings --recursion-level 0 --output failures --check-extern --stdin
}

grep_links() {
    for file in $(find "${TARGETS[@]}"); do
        grep -oE "\b(https?://|www\.)[^\[\(\)\"]+\b" "${file}"
    done
}

valid_links() {
    local all_links="$(grep_links | sort | uniq | tr ' ' '\n')"
    local ignore_links="$(echo "${IGNORE_URLS[@]}" | sort | uniq | tr ' ' '\n')"
    comm -3 <(echo "$all_links") <(echo "$ignore_links")
}

check_links <<< "$(valid_links)"

if [[ "$?" != "0" ]]; then
    echo "Found broken links, see output above"
    exit 1
fi

