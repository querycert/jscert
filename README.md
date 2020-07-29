# JsAst

This is a minimal JavaScript syntax tree carved out of the
[JsCert](https://github.com/jscert/jscert) project.

## Installation

JsAst depends on:
- Coq (version 8.11.2) or later

### From opam

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-jsast
```

### Local with opam

In this directory:

```
opam install .
```

### From source

To compile, do:
```
make
```

To install as a Coq user contribution, do:
```
make install
```

