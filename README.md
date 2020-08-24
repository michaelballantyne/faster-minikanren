# miniKanren-with-symbolic-constraints

A revision of https://github.com/webyrd/miniKanren-with-symbolic-constraints/ for better performance. Up to 10x faster for large queries involving heavy use of constraints.

Includes `==`, `=/=`, `symbolo`, `numbero`, and `absento`.

*** Update (WEB, 21 August 02018): `absento` is now general--the first argument can be any legal miniKanren term, and needn't be ground.  Previously, `faster-miniKanren` required the first argument to `absento` be an `eqv?`-comparable ground atom.  Thanks to Michael Ballantyne for pointing out how to remove this restriction.

Eigen was removed.

## Running

### Racket

#### From the Package Server

This is available on the [Racket package server](https://pkgn.racket-lang.org/package/faster-minikanren), so it can be installed with Racket's package manager:

```
raco pkg install faster-minikanren
```

After which you can import it in a Racket module with

```
(require minikanren)
```

#### From a checkout of this repository

Alternatively the files from this repository can be used directly:

```
(require "mk.rkt")
```

to load tests:

```
racket test-all.rktl
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

### Guile

After putting the directory in Guile's load path:

```
(use-modules (faster-miniKanren mk-guile))
```

To run tests:

```
guile test-guile.scm
```

## Other code

`numbers.scm` includes the relational number system described in The Reasoned Schemer.

`simple-interp.scm` includes a small relational interpreter capable of generating quines, as presented in "miniKanren, Live and Untagged" (http://webyrd.net/quines/quines.pdf)

`full-interp.scm` includes a more advanced relation interpreter supporting function definition with `letrec` and a relational pattern matcher.

`matche.scm` includes a pattern matching syntax that expands to unification.

Each of these files is also wrapped in a corresponding `.rkt` file as a Racket module.


## What makes it fast?

The https://github.com/webyrd/miniKanren-with-symbolic-constraints/ implementation doesn't make much effort to be fast.

This version uses faster data representations and a different algorithm for checking constraints. It also drops some features I don't understand and don't know how to implement efficiently: eigen, and the more general version of absento.

### Substitution Representation

We use a persistent map with log time access and update rather than an association list. On Racket we use the built-in immutable hash to take advantage of its C-level implementation in the runtime (mk.rkt). On other Scheme systems we use a trie implementation that organizes elements according to the binary digits of a fixnum identifying the variable (`mk-vicare.scm`). Note that the tree starts lookup at the low-order bits, so it should remain well-balanced as variables with sequential identifiers are added. The lookup is more expensive for more recently added variables (with higher-valued identities), however.

Using a log-time persistent map seems to be better than an association list when the substitution is larger than about 100 elements in size. The improvement from linear time to log time is very important for large substitutions. Association lists are faster for small substitutions, but the effect here is only constant time. As such we prefer the log-time persistent map for more reliable performance across workloads.

Plenty of other miniKanren use log-time persistent maps for their substitutions; core.logic (https://github.com/clojure/core.logic) and veneer (https://github.com/tca/veneer) certainly do.

These particular data structure choices may not be optimal; we haven't recently evaluated a broad array of map types. There's a paper on it concluding that skew binary random access lists might be the best: https://users.soe.ucsc.edu/~lkuper/papers/walk.pdf

### set-var-val!

Regardless of the choice of substitution representation, lookup is somewhat expensive. In certain circumstances we can avoid storing the value of a logic variable in the substitution at all and avoid that cost.

Consider the implementation of `appendo`:

```
(define (appendo l s out)
  (conde
    [(== l '()) (== s out)]
    [(fresh (a d res)
       (== `(,a . ,d) l)
       (== `(,a . ,res) out)
       (appendo d s res))]))
```

Note that `a`, `d`, and `res` are used in unifications directly after they are allocated with `fresh`. Depending on the modality of the use of `appendo`, these variables may immediately receive values during those unifications. In that case, it is not possible for the variable to take on different values in different branches of the search tree; they receive their value before the search tree branches.

Based on this observation, we store the values of variables that are assigned values immediately after they are allocated (before the computation branches from a `conde`) within a field of the variable object itself, rather than within the substitution. Variables are represented by a vector holding:

1. a value field, which initially contains an "unbound" value indicating that the variable is either unbound or bound in the substitution, but is mutated when a value is assigned in this optimized way.
2. a scope number, used to determine whether the search tree has branched since the variable was allocated. A scope counter is passed through the search and incremented whenever it branches; when a variable is allocated the current scope counter is stored in the variable.
3. a numeric id, used as a key for the binary trie substitution representation discussed above.

I'm not aware of this optimization being used in other miniKanren implementations. Unification in prolog certainly avoids expensive lookups by direct mutation, but prolog implementations don't maintain substitutions for multiple branches of the search in the same way miniKanren does.

### Constraint Representation and Solving

The key optimization is in the representation of disequality, absento, and type constraints. All constraint data is stored in a map associating variables with constraints that they participate in, and constraints are only processed when a variable's domain has been constrained in a way that may violate the constraint. This is related to the attributed variable feature found in prolog systems.

In contrast, other miniKanren implementations often just keep a big list of constraints and recheck and simplify the whole list every time a unification happens, which gets very expensive when there are many constraints. I know that https://github.com/webyrd/miniKanren-with-symbolic-constraints/ and https://github.com/tca/veneer take this approach. I don't understand core.logic's implementation well enough to be sure what is done there, but I think it does the same but with a little extra logic to specify the dependencies between constraint types. The big list of constraints approach does allow for easier extensibility with user-defined constraints.

In our implementation, each logic variable has constraint information associated with it with three parts: type, disequality, and absento constraint information. Every time a variable is instantiated, its constraint information is examined. Constraints attached to other variables that are not instantiated, however, do not need to be checked.

#### Type constraints

`symbolo` and `numbero` assert that a term will be of a particular atomic type. Because there are infinitely many values of each of these types, this constraint thankfully doesn't interact with disequality; there is no way that adding the fact that a term is a symbol or a number on top of existing disequality constraints (but not other type constraints or specific values) can cause failure.

Thus these constraints just check that the term is not already a ground value with the wrong type and that the constraint store does not already record a conflicting type. If that passes and the term is still a variable, then the type is recorded in the type part of the variable's entry in the constraint store. See `type-constraint` in the implementation.

#### Disequality

A disequality constraint should fail if its arguments are instantiated such that there is no longer any way for them to be distinct. It can be discarded as satisfied if its arguments are instantiated such that they must definitely be distinct.

Given the other constraints available in this implementation, the only way for a disequality to fail is if the arguments are instantiated to be fully ground and equal, again because it is not possible to constrict the range of a logic variable to a finite range of values without fully instantiating it.

Disequality constraints can be normalized as a disjunction of component atomic parts. Each atomic constraint states a disequality between one fresh logic variable and a term (which may be another fresh logic variable, or may be another type of term). The overall constraint succeeds as long as at least one of its component disequalities is true, and fails if every one of its component disequalities is false.

Consider this disequality:

```
(fresh (a b c d)
  (=/= `(,a . ,b) `(,c . ,d)))
```

The component disequalities are:

```
(=/= a c)
```

and

```
(=/= b d)
```

If we find out that `a` is `5 and `c is `8`, then that component disequality is true and the overall disequality is true, regardless of the values of `b` and `d`.

If instead we found out that `a` is `5` and `c` is also `5`, then the value of the overall constraint is still unknown. As long as `b` and `d` are still uninstantiated, the constraint should not fail.

A consequence of these properties is that we only need to attach information about the constraint to the logic variables involved in one of the component disequalities. No matter what happens with the other components, if the logic variables in the selected component disequality remain uninstantiated the constraint does not need to fail. Limiting the variables that we attach the disequality to reduces the cost associated with re-checking the constraints as unifications happen.

If the component disequality involves a variable and a non-variable term we only need to attach information to the variable, as it can only become equal to the non-variable term by becoming instantiated. If the component disequality involves a variable and another variable, we must attach information to *both* variables, as a unification of the two could instantiate either variable to point to the other.

The component disequalities can be found by attempting unification of the arguments to the disequality and recording the associations that would be added to the substitution.

#### Absento

Information about absento constraints is attached to each uninstantiated variable in a term. Here the overall constraint is a *conjunction* of individual components; if the atom specified in the constraint is found in any part of the term, the constraint must fail. When a variable with absento information is instantiated, it may:

* eliminite the component if the new value is an atom that is different than the atom specified by the constraint
* cause failure if the new value is the same atom as that specified by the constraint
* propagate the constraint to component parts if the new value is a pair

Again, the constraint is only examined when a variable that it concerns is instantiated.
