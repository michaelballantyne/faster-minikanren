(eval-when (compile) (optimize-level 3))

(module mk (run run* defrel == =/= fresh conde symbolo numbero stringo absento test)
  (import (except scheme subst))
  (implicit-exports #t)
  (include "./mk-vicare.scm")
  (include "./mk.scm")
  (include "./test-check.scm"))

