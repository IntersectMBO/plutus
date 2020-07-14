# This is a copy of the one from the module, it's here so that
# it's easier for people not using Nix to build the site.

from sphinxcontrib.domaintools import *

def hs_domain():
    return custom_domain('HaskellDomain',
        name  = 'hs',
        label = "Haskell",

        elements = dict(
            hsobj = dict(
                objname = "Haskell entity",
            ),
            hstype = dict(
                objname = "Haskell type",
            ),
            hsval = dict(
                objname = "Haskell value",
            ),
            hsmod = dict(
                objname = "Haskell module",
            ),
        )
    )

def setup(app):
    app.add_domain(hs_domain())
