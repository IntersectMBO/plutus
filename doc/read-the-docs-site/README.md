# Plutus and Marlowe documentation site
 
This is a sphinx site. 
Assuming you're in a `nix-shell`, from the top-level, you can either build the site directly:

```
sphinx-build -j 4 -n doc doc/_build 
```

And then open `doc/_build/index.html` in your browser.


Or you can get yourself a development server with live reload on `http://127.0.0.1:8000`:

```
sphinx-autobuild -j 4 -n doc doc/_build 
```

Or you can use Nix which will also build the Haddock for the project and link it in:

```
nix build -f default.nix docs.site
```

The doc site from main is built automatically and hosted [here](https://plutus.readthedocs.io/en/latest).

Additionally, the site is built for all PRs, and a link to a preview can be found in the PR statuses.