(TeX-add-style-hook
 "PlutusCoreTypeCorrectness"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("subfiles" "../main.tex")))
   (TeX-run-style-hooks
    "latex2e"
    "subfiles"
    "subfiles10")
   (LaTeX-add-labels
    "fig:Plutus_core_contexts"
    "fig:Plutus_core_kind_synthesis"
    "fig:Plutus_core_type_synthesis"))
 :latex)

