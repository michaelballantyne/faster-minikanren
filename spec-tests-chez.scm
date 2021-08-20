(module test ()
             (import (except scheme subst))
             (include "./mk-vicare.scm")
             (include "./mk.scm")
             (include "spec-tests.scm"))
(exit)

;(pretty-print
  ;(expand/optimize
    ;'(module test ()
             ;(import (except scheme subst))
             ;(include "./mk-vicare.scm")
             ;(include "./mk.scm")
             ;(include "spec-tests.scm"))))
