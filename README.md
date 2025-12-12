# About
BRAT is a functional programming language designed for writing quantum experiments. For an introduction to BRAT, see the [extended abstract](papers/brat-planqc-2024.pdf) submitted to PLanQC 2024.

# Installation
To build BRAT from source, you will need:
- GHC 9.6.4 (can be installed with the `ghcup` tool)
- The `stack` build tool for Haskell

Then, navigate to the `brat` directory and run `stack install`.

This will add the `brat` and `brat-lsp` binaries  to `~/.local/bin`, and copy configuration for the emacs editor mode to `~/.local/share/brat/`.

There is also a plugin for the VS Code editor. To install this, look at `vscode/README.md`.

# Usage
### Typechecking
By default, the installed `brat` executable  will typecheck a program given as an argument, e.g.:
```sh
brat my-program.brat
```
which, if `my-program` typechecks, will print out the parsed versions of the declarations and a list of remaining holes.

### Compiling
The `--compile` flag can be used to compile the BRAT program to the [hugr](https://github.com/Quantinuum/hugr) IR and print the JSON representation to the command line.

### Validating
There is a tool in the root of the repository called `hugr_validator` (install by `cd hugr_validator && cargo install --path .`) which is used to check that the JSON output from BRAT constitutes a valid hugr. This is invoked by:
```sh
brat --compile my-program.brat | hugr_validator
```

# Development
Before opening a PR, make sure to run hlint on your code, using:
```sh
make hlint
```
or try to automatically apply fixes with:
```sh
make hlint-fix
```


# Reference
The [`brat/examples`](brat/examples) directory contains some examples of BRAT programs.
For example:
- Quantum teleportation: [teleportation.brat](brat/examples/teleportation.brat)
- Quantum Fourier transform: [teleportation.brat](brat/examples/teleportation.brat)
- Magic State Distillation: [magic-state-distillation.brat](brat/examples/magic-state-distillation.brat)
- Simple Repeat-Until-Success: [rus.brat](brat/examples/rus.brat)
- Ising Hamiltonian: [ising.brat](brat/examples/ising.brat)

This directory also contains tests of syntax features which, while terse, may serve as a reference in the short term.
For example:
- [unified.brat](brat/examples/unified.brat) contains some functional programs
- [dollar_kind.brat](brat/examples/dollar_kind.brat) tests polymorphism over kernel types
- [tups.brat](brat/examples/tups.brat) tests heterogenous lists
- [compjuxt.brat](brat/examples/compjuxt.brat), `brat/examples/composition.brat` contain tests for diagrammatic syntax
- [pass.brat](brat/examples/pass.brat) tests the 'passthrough' (`..`) operator
- [portpulling.brat](brat/examples/portpulling.brat) demonstrates port pulling
