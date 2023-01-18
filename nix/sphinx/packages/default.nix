{ inputs, cell }@block:
{

  sphinx-markdown-tables = import ./sphinx-markdown-tables.nix block;

  sphinx-toolchain = import ./sphinx-toolchain.nix block;

  sphinxcontrib-bibtex = import ./sphinxcontrib-bibtex.nix block;

  inherit (import ./sphinxcontrib-haddock.nix block)

    sphinxcontrib-domaintools

    sphinxcontrib-haddock

    sphobjinv;

  sphinxemoji = import ./sphinxemoji.nix block;

  read-the-docs-site = import ./read-the-docs-site.nix block;

}
