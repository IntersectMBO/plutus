# Developing the code

An appropriate environment for developing a package can be entered using `nix-shell` in the package directory. This
includes all the dependencies for the package and `cabal`, so you should be able to `cabal build` a package after
doing this.

## Updating the generated Haskell package set

`pkgs/default.nix` contains a generated package set with all the dependencies for this project.

You should regenerate this if you change any dependencies in cabal files. To do this, run `pkgs/generate.sh`.

## Adding a new package

You need to do a few things when adding a new package, in the following order:
- Add the cabal file.
- Add the package to `stack.yaml`.
- Update the generated package set (see above).
- Add the project to `plutusPkgList` in `lib.nix`.
    - This will ensure it gets built by CI and so on.

You should at least be able to run `nix build -f default.nix localPackages.<package name>` successfully at the root. You can use `nix log -f default.nix localPackages.<package name>` if you want to check the build output.

## Code style

We use `stylish-haskell` and `hlint`, and enable a large number of GHC warnings.
- These are run by the CI, so if you don’t use them your PR will not go green. To avoid annoyance, set up your editor to run them automatically.
- It’s fine to be aggressive about disabling `hlint` rules that don’t provide value, but check with the team before doing this. Err on the side of disabling them globally rather than for specific files, so we stay consistent.
- Try and make sure that you do not have any compiler warnings - this is not currently checked by the CI, but may be in future.

# Issues

General issues can be opened on the [GitHub Issue tracker](https://github.com/input-output-hk/plutus/issues).

## IOHK developers

We track our issues on the [IOHK YouTrack instance](https://iohk.myjetbrains.com/youtrack/issues/CGP).

# Submitting changes

## Pull requests

All code changes go through pull requests.
- Make your PR from the main repository if possible, this is necessary for the Buildkite CI to trust you.
    - Making a PR from a fork is acceptable, you will need to do this if you don't have write access to the main repository.
- Try to name branches systematically.
    - If you're the only person working on the branch, prefix the branch name with your GitHub ID.
    - If the PR is in response to a YouTrack ticket, include the ticket name.
    - Things can be easier to find if you use hierarchical names containing slashes.
    - For example: `some_user/CGP-994/add-linear-types`.
- PRs exist to be reviewed - design them with a reader in mind!
    - Include the ticket name in the PR title where possible.
    - Write a helpful PR description that explains what’s in the PR and why, and draws attention to anything of particular note, references related tickets etc.
    - Consider rebasing your PRs before submitting to structure them into a few logical commits that can be reviewed separately.
Keep PRs to a single topic.
    - If you find yourself making unrelated changes, pull those commits out into another PR and submit them separately (i.e. do not include them in the original PR)
    - If you can’t remove unrelated changes from your PR (because you depend on them), then add a note that your PR depends on the other one and should not be merged before it. You can still put it up for review.
    - Take especial care to manage changes that are likely to have many conflicts (like formatting or refactoring changes) in their own PRs.
- Submit PRs in a “finished” state. If you want to use a PR to let people review a WIP branch, make sure to label it obviously.
- Ideally, every commit should pass CI
    - This makes tools like `git bisect` much more reliable.
    - You can achieve this by rebasing and force-pushing, or by requesting a squash merge.
- Use your judgment when requesting review
    - Almost all PRs should have a review, and ideally the reviewer should merge them. If they’re happy but haven’t merged, or you need to fix conflicts, then it’s fine to merge the PR yourself.
        - Documentation-only PRs can be merged without a review
        - In some cases very small PRs like trivial bug fixes can also be merged without a review
    - PRs with changes to code that another team member is currently working on should always request a review from the affected team member.
- Force-pushing PRs is okay, this will mostly do the right thing in Github. Do this if you’re applying fixups, or you’ve done a series of additional commits that you want to squash down before merging.
    - Alternatively, request a squash merge.
- Comment if you want attention from someone (e.g. a re-review after changes). Github does not make it easy to signal this state otherwise, and people may not be notified if you just push commits.

## Code review

- Try to review PRs where your review is requested within a few days. This should be nearly-top-priority work.
- If you don’t understand something then ask for an explanation.
    - For the author: this explanation should ideally be added as a comment - you’re going to write it anyway, and future readers are likely to be just as confused as the reviewer.

# Continuous integration

We have two pieces of CI at the moment: some tests are run using Nix on Hydra, and some are run on Buildkite.
- All the projects will be built, as well as the tests in `default.nix`.
- Pull requests cannot be merged without the CI going green.
    - Because the CI is not necessarily run on the merge commit that is created when the PR is merged, it is possible that merging a green PR can result in the CI being broken on master. This shouldn't happen frequently, but be aware that it's possible.
- The CI should report statuses on your PRs with links to the logs in case of failure.
