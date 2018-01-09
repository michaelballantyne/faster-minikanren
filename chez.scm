(eval-when (compile) (optimize-level 3))

(module mk (run run* == =/= fresh conde symbolo numbero absento test)
  (import (except scheme subst))
  (implicit-exports #t)
  (include "./mk-vicare.scm")
  (include "./mk.scm")
  (include "./test-check.scm"))

