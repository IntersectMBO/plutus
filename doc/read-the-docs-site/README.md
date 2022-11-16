# Plutus and Marlowe documentation site

This is a sphinx site.

Run `nix develop` to enter a development shell with `sphinx-build` and `sphinx-autobuild`.

The following commands are also available:

- `autobuild-docs`          
  Start a development server with live reload on `http://localhost:8000`
- `build-docs`             
  Build the docs locally in `_build/index.html`
- `serve-docs`   
  Build the full site with nix (including Haddock) and serve it on `http://localhost:8002`

The doc site from main is built automatically and hosted [here](https://plutus.readthedocs.io/en/latest).

Additionally, the site is built for all PRs, and a link to a preview can be found in the PR statuses.
