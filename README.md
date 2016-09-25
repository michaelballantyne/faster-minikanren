# miniKanren-with-symbolic-constraints

A revision of https://github.com/webyrd/miniKanren-with-symbolic-constraints/ for better performance. Up to 10x faster for large queries involving heavy use of constraints.

Includes `==`, `=/=`, `symbolo`, and `numbero`. `absento` is included, but the argument is required to be an eqv-comparable ground atom.

Eigen was removed.

## Running

### Racket

```
(require "mk.rkt")
```

to load tests:

```
racket test-all.rktl
```

This repository is also a package for the Racket package manager. When it is installed, it may be used with:

```
(require minikanren)
```

### Vicare and Chez Scheme

```
(load "mk-vicare.scm")
(load "mk.scm")
```

To run tests:

```
(load "mk-vicare.scm")
(load "mk.scm")
(load "test-all.scm")
```

## Other code

`numbers.scm` includes the relational number system described in The Reasoned Schemer.

`simple-interp.scm` includes a small relational interpreter capable of generating quines, as presented in "miniKanren, Live and Untagged" (http://webyrd.net/quines/quines.pdf)

`full-interp.scm` includes a more advanced relation interpreter supporting function definition with `letrec` and a relational pattern matcher.

`matche.scm` includes a pattern matching syntax that expands to unification.

Each of these files is also wrapped in a corresponding `.rkt` file as a Racket module.

