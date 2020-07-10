# Configuration file for the Sphinx documentation builder.
#
# This file only contains a selection of the most common options. For a full
# list see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html

# -- Path setup --------------------------------------------------------------

# If extensions (or modules to document with autodoc) are in another directory,
# add these directories to sys.path here. If the directory is relative to the
# documentation root, use os.path.abspath to make it absolute, like shown here.
#
# import os
# import sys
# sys.path.insert(0, os.path.abspath('.'))


# -- Project information -----------------------------------------------------

project = 'Plutus Platform'
copyright = '2020, IOHK'
author = 'IOHK'

import sys, os

sys.path.append(os.path.abspath('exts'))

# -- General configuration ---------------------------------------------------

# Add any Sphinx extension module names here, as strings. They can be
# extensions coming with Sphinx (named 'sphinx.ext.*') or your custom
# ones.
extensions = [
  'hs_domain',
  'sphinx.ext.intersphinx'
]

# Add any paths that contain templates here, relative to this directory.
templates_path = ['_templates']

# List of patterns, relative to source directory, that match files and
# directories to ignore when looking for source files.
# This pattern also affects html_static_path and html_extra_path.
exclude_patterns = []

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

# -- Options for HTML output -------------------------------------------------

# The theme to use for HTML and HTML Help pages.  See the documentation for
# a list of builtin themes.
#
html_theme = 'sphinx_rtd_theme'

# Add any paths that contain custom static files (such as style sheets) here,
# relative to this directory. They are copied after the builtin static files,
# so a file named "default.css" will overwrite the builtin "default.css".
html_static_path = []
