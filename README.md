# An Exceptional Type Theory in Coq

This plugin allows to automatically translate Coq terms in such a way that
they can now use exceptions. This can be useful for programming, e.g. to allow
failure locally and prove after the fact that assuming a few properties the
translated term does not fail, without endangering reduction as a monadic
translation would do. This can also be used to extend the logical power of Coq
itself, allowing to prove a few semi-classical principles amongst which
independent of premises or Markov's rule.

A draft paper describing the translation can be found
[here](https://hal.inria.fr/hal-02189128).

# Compilation

This requires Coq 8.7. If the `COQBIN` variable is correctly set, a `make`
invokation should be enough.

# Use of the plugin

The plugin adds four new commands which we describe below.

## Effect Translate

```
Effect Translate GLOBAL [using GLOBAL].
```

This command translates the given global definition into the type theory with
exception. The resulting term is parameterized over the type of exceptions used.
It can be restricted to a particular exception type by adding the `using`
clause.

Beware, the resulting theory is inconsistent in general. You need to show
parametricity to ensure consistency, see below.

## Effect Implementation

```
Effect Definition IDENT : TYPE [using GLOBAL].
```

This command opens the proof mode and ask the user to provide a proof of
TYPE in the effectful translation. When the proof is complete, the axiom IDENT
is added to Coq, a term IDENTᵉ is defined with the content of the proof, and
the axiom IDENT is registered to be mapped to IDENTᵉ through the effectful
translation.

# Examples

The repository contains a few examples in the `tests` folder.

# Caveat

Sections are not handled.

The translation does not handle universe polymorphism, and primitive records
are handle in a very basic way, without catch principles and the modality.

# License

This software is licensed under the WTFPL 2.0.
