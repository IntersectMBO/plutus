TARGETS=(
    .github/ISSUE_TEMPLATE/bug_report.yml
    .github/ISSUE_TEMPLATE/feature_request.yml
    .github/PULL_REQUEST_TEMPLATE.md
    .github/SECURITY.md
    CODE_OF_CONDUCT.md
    CONTRIBUTING.adoc
    LICENSE
    NOTICE
    README.adoc
    RELEASE.adoc
    STYLEGUIDE.adoc
)

FAILED=0

for file in "${TARGETS[@]}"; do 
    echo "Checking ${file}"
    grep -oE "\b(https?://|www\.)[^\[\(\)\"]+\b" "${file}" \
        | linkchecker --no-warnings --recursion-level 0 --output failures --check-extern --stdin \
        --ignore-url https://img.shields.io/matrix/plutus-core%3Amatrix.org # For some reason linkchecker fails to check this URL though it is valid
    if [ $? -ne 0 ]; then 
        echo "${file} has broken links, see output above"
        FAILED=1
    fi 
done 

exit "${FAILED}"
