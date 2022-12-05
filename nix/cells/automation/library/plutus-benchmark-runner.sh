# ci-plutus-benchmark: Run benchmarks on 2 branches, compare the results and
# add a comment on the corresponding PR on GitHub.
#
# USAGE: 
# In order to trigger benchmarking for an open PR, add `/benchmark` as a comment to
# the PR. The command will be acknowledged with a :rocket: reaction and when done a bot will
# add the results as comment to the same PR.
#
# NOTES:
# (1) In order to post a comment to GitHub the buildkite runner needs to provide a
#     GitHub token with permissions to add comments in '/run/keys/buildkite-github-token'
#     otherwise this will fail.
# (2) The `cabal update` command below is neccessary because while the whole script
#     is executed inside a nix-shell, this environment does not provide the hackage
#     record inside .cabal and we have to fetch/build this each time since we want
#     to run this in a clean environment.
# (3) The `jq` invocation below is necessary because we have to POST the PR comment
#     as JSON data (see the curl command) meaning the script output has to be escaped
#     first before we can insert it.

set +e

if [ -z "$PR_NUMBER" ] ; then
   echo "[ci-plutus-benchmark]: 'PR_NUMBER' is not set! Exiting"
   exit 1
fi
if [ -z "$BENCHMARK_NAME" ] ; then
   echo "[ci-plutus-benchmark]: 'BENCHMARK_NAME' is not set! Exiting"
   exit 1
fi

PR_BRANCH_REF=$(git rev-parse --short HEAD)

echo "[ci-plutus-benchmark]: Processing benchmark comparison for benchmark '$BENCHMARK_NAME' on PR $PR_NUMBER"

echo "[ci-plutus-benchmark]: Updating cabal database ..."
nix develop --command cabal update

echo "[ci-plutus-benchmark]: Running benchmark for PR branch ..."
nix develop --command cabal bench $BENCHMARK_NAME >bench-PR.log 2>&1

echo "[ci-plutus-benchmark]: Switching branches ..."
git fetch 
git checkout "$(git merge-base FETCH_HEAD origin/master)"
BASE_BRANCH_REF=$(git rev-parse --short FETCH_HEAD)

echo "[ci-plutus-benchmark]: Clearing caches with cabal clean ..."
nix develop --command cabal clean

echo "[ci-plutus-benchmark]: Running benchmark for base branch ..."
nix develop --command cabal bench $BENCHMARK_NAME >bench-base.log 2>&1

echo "[ci-plutus-benchmark]: Comparing results ..."
{
# The blank line is important, otherwise Github doesn't render markdown in the body of the details element.
# See https://gist.github.com/ericclemmons/b146fe5da72ca1f706b2ef72a20ac39d for examples
cat <<EOF 
Comparing benchmark results of '$BENCHMARK_NAME' on '$BASE_BRANCH_REF' (base) and '$PR_BRANCH_REF' (PR)

<details>
<summary>Results table</summary>

EOF
bash ./plutus-benchmark/bench-compare-markdown bench-base.log bench-PR.log "${BASE_BRANCH_REF:0:7}" "${PR_BRANCH_REF:0:7}"
echo -e "</details>"
} > bench-compare-result.log

jq -Rs '.' bench-compare-result.log >bench-compare.json
if [ -v GITHUB_TOKEN ] ; then
   echo "[ci-plutus-benchmark]: Posting results to GitHub ..."
   curl -s -H "Authorization: token $(<$GITHUB_TOKEN)" -X POST -d "{\"body\": $(<bench-compare.json)}" "https://api.github.com/repos/input-output-hk/plutus/issues/${PR_NUMBER}/comments"
else
   echo "[ci-plutus-benchmark]: GITHUB_TOKEN not set, not posting results to GitHub"
fi
