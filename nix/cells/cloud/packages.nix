# TODO(std) delete this file before merging
{ cell, inputs }:
{
  test-run-plutus-benchmark = cell.library.plutus-benchmark-runner {
    PR_NUMBER = "4956";
    PR_COMMIT_SHA = "c6c6cd04c0d3ea6e6d041ff7f75ab9b92467dbef";
    BENCHMARK_NAME = "nofib";
  };
}
