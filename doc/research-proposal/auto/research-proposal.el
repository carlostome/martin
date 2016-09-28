(TeX-add-style-hook
 "research-proposal"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("scrartcl" "11pt" "a4paper")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("inputenc" "utf8") ("babel" "english") ("cleveref" "noabbrev")))
   (add-to-list 'LaTeX-verbatim-environments-local "lstlisting")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "lstinline")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "lstinline")
   (TeX-run-style-hooks
    "latex2e"
    "scrartcl"
    "scrartcl11"
    "inputenc"
    "babel"
    "geometry"
    "amsmath"
    "amssymb"
    "amsthm"
    "xcolor"
    "graphicx"
    "todonotes"
    "enumitem"
    "cleveref")
   (LaTeX-add-bibliographies
    "literature"))
 :latex)

