# Installation & Use

This folder contains the experimental partial proof results achieved. Many of
the definitions and propositions may be ill-defined, incomplete and incorrect.
Use with caution and scepticism.

A number of Coq libraries was used:

- Coquelicot: Contains definitions for derivatives
- Equations: Dependent pattern matching a la Agda

Instructions for installing these using opam:

```
opam install coq-coquelicot
opam install coq-equations
```

Unicode characters are used liberally, please make sure you have a font
installed which supports these. Recommended dev environment consists of VSCode
with the VSCoq extension for Coq IDE-like functionality and the `latex-input`
plugin for Unicode input.

Tested with Coq version 8.11.1

When changing import/file structure rebuild the `Makefile` file using
`coq_makefile -Q . AD *.v > Makefile`.
