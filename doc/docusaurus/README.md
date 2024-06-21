# Website

This website is built using [Docusaurus](https://docusaurus.io/), a modern static website generator.

### Installation

```
$ yarn
```

### Local development

```
$ yarn start
```

This command starts a local development server and opens up a browser window. Most changes are reflected live without having to restart the server.

### Build

```
$ yarn build
```

This command generates static content into the `build` directory and can be served using any static contents hosting service.

### Deployment

Go to the [docusaurus-site.yml](https://github.com/IntersectMBO/plutus/actions/workflows/docusaurus-site.yml) workflow and click `Run workflow` on the right.

This will build and publish the website to the `gh-pages` branch at https://intersectmbo.github.io/plutus/docs.