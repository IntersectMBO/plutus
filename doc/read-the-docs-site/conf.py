

import sys
import os
import sphinx_rtd_theme
import recommonmark

from recommonmark.transform import AutoStructify
from os.path import abspath, join, dirname

sys.path.insert(0, abspath(join(dirname(__file__))))
sys.path.append(os.path.abspath('exts'))

# -- RTD configuration ------------------------------------------------

on_rtd = os.environ.get("READTHEDOCS", None) == "True"

# This is used for linking and such so we link to the thing we're building
rtd_version = os.environ.get("READTHEDOCS_VERSION", "latest")
if rtd_version not in ["stable", "latest"]:
    rtd_version = "stable"

# -- Project information -----------------------------------------------------

project = 'Plutus Core and Plutus Tx User Guide'
copyright = '2022, IOHK'
author = 'IOHK'

# The full version, including alpha/beta/rc tags
release = '1.0.0'

# -- General configuration ---------------------------------------------------
master_doc = 'index'
# Add any Sphinx extension module names here, as strings. They can be
# extensions coming with Sphinx (named 'sphinx.ext.*') or your custom
# ones.

extensions = [
    "sphinx_rtd_theme",
    'recommonmark',
    'sphinx_markdown_tables',
    'sphinxemoji.sphinxemoji',
    "sphinx.ext.intersphinx",
    'sphinxcontrib.plantuml',
    'sphinxcontrib.bibtex',
    'hs_domain',
]

bibtex_bibfiles = ['bibliography.bib']
bibtex_default_style = 'plain'

# Amazingly, RTD actually provide plantuml
if on_rtd:
    plantuml = 'java -Djava.awt.headless=true -jar /usr/share/plantuml/plantuml.jar'

primary_domain = 'hs'

haddock_mapping = {}
haddock_dir = os.getenv('SPHINX_HADDOCK_DIR', None)
if haddock_dir:
  for entry in os.scandir(haddock_dir):
    if entry.is_dir():
      html_dir = os.path.join(entry.path, 'html')
      inv_file = os.path.join(html_dir, 'objects.inv')
      if os.path.exists(inv_file):
        haddock_mapping[entry.name] = (html_dir, inv_file)

intersphinx_mapping = haddock_mapping


# Add any paths that contain templates here, relative to this directory.
templates_path = ['_templates']
html_static_path = ['_static']

source_suffix = {
    '.rst': 'restructuredtext',
    '.md': 'markdown',
}

# List of patterns, relative to source directory, that match files and
# directories to ignore when looking for source files.
# This pattern also affects html_static_path and html_extra_path.
exclude_patterns = [
    'haddock', # Otherwise it tries to pick up the README.md's in the Haddock doc!
    'README.md'
]

# -- Options for HTML output -------------------------------------------------

# The theme to use for HTML and HTML Help pages.  See the documentation for
# a list of builtin themes.
#
html_theme = "sphinx_rtd_theme"

html_theme_options = {
    'logo_only': False,
    'display_version': False,
    'prev_next_buttons_location': 'bottom',
    'style_external_links': False,
    'style_nav_header_background': '#fcfcfc',
    # Toc options
    'collapse_navigation': False,
    'sticky_navigation': True,
    'navigation_depth': 4,
    'includehidden': True,
    'titles_only': False
}

html_logo = "cardano-logo.png"

html_context = {
  "display_github": True, # Add 'Edit on Github' link instead of 'View page source'
  "github_user": "input-output-hk",
  "github_repo": "plutus",
  "github_version": "master",
  "conf_py_path": "/doc/",
  "source_suffix": source_suffix,
}

# -- Custom Document processing ----------------------------------------------

def setup(app):
    app.add_config_value('recommonmark_config', {
            'enable_auto_doc_ref': False,
            'enable_auto_toc_tree': False,
            }, True)
    app.add_transform(AutoStructify)
    app.add_css_file("theme_overrides.css")
