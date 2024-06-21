# Website

This website is built using [Docusaurus](https://docusaurus.io/), a modern static website generator.

### Development 

Follow the [nix setup guide](https://github.com/input-output-hk/iogx/blob/main/doc/nix-setup-guide.md) (this is recommended) or alternatively use your local `yarn` installation.

If using nix and while inside this directory, run `nix develop` to enter the shell.

Now you can use `yarn` for development:
```bash 
yarn # to install dependencies 
yarn build # to build the website 
yarn start # for live development on localhost
```

### Deployment

Go to the [docusaurus-site.yml](https://github.com/IntersectMBO/plutus/actions/workflows/docusaurus-site.yml) workflow and click `Run workflow` on the right.

This will build and publish the website to [GitHub pages](https://intersectmbo.github.io/plutus/docs).