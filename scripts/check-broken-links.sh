TARGETS=(
    .github/{ISSUE_TEMPLATE/*,*.md,*.yml} 
    **/{LICENSE,NOTICE,README.md,TRIAGE.md} 
    CODE_OF_CONDUCT.md 
    *.adoc
)

# For some reason linkchecker fails to check these URLs though they are valid
IGNORE_URLS=(
    --ignore-url="^https://pvp\.haskell\.org.*" 
    --ignore-url="^https://img\.shields\.io/matrix/plutus-core%3Amatrix\.org.*" 
)

FAILED=0

grep_links() {
    grep -oE "\b(https?://|www\.)[^\[\(\)\"]+\b" "$1"
}

check_links() {
    linkchecker --no-warnings --recursion-level 0 --output failures --check-extern "${IGNORE_URLS[@]}" --stdin 
}

for file in $(find "${TARGETS[@]}"); do 
    echo "Checking ${file}"
    grep_links "${file}" | check_links
    if [ $? -ne 0 ]; then 
        echo "${file} has broken links, see output above"
        FAILED=1
    fi 
done 

exit "${FAILED}"
