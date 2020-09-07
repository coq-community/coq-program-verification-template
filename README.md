# Coq Program Verification Template

[![CI][action-shield]][action-link]

[action-shield]: https://github.com/palmskog/coq-program-verification-template/workflows/CI/badge.svg?branch=master
[action-link]: https://github.com/palmskog/coq-program-verification-template/actions?query=workflow%3ACI




Template project for program verification in Coq.
Uses the Verified Software Toolchain and a classic binary
search program in C as an example.

## Meta

- Author(s):
  - Karl Palmskog
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.11 or later
- Additional dependencies:
  - [CompCert](http://compcert.inria.fr) 3.7
  - [Verified Software Toolchain](https://vst.cs.princeton.edu) 2.6
- Coq namespace: `ProgramVerificationTemplate`

## Building instructions

### Installing dependencies

The recommended way to install Coq and other dependencies is via
[OPAM](https://opam.ocaml.org/doc/Install.html), for example:
```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.12.0 coq-vst.2.6 coq-compcert
```

### Obtaining the project

```shell
git clone https://github.com/palmskog/coq-program-verification-template.git
cd coq-program-verification-template
```

### Option 1: building the project using coq_makefile

```shell
make   # or make -j <number-of-cores-on-your-machine> 
```

### Option 2: building the project using Dune

``` shell
dune build
```

### Compiling the program using CompCert (optional)

```shell
ccomp -o bsearch src/binary_search.c
```

## File and directory structure

### Core files

- [`src/binary_search.c`](src/binary_search.c): C program that performs binary
  search in a sorted array, adapted from [Joshua Bloch's Java version][binary-search-url].
- [`theories/binary_search.v`](theories/binary_search.v): Coq representation
  of the binary search C program in [CompCert's Clight language][compcert-c-url].
- [`theories/binary_search_theory.v`](theories/binary_search_theory.v): General
  Coq definitions and facts relevant to binary search.
- [`theories/binary_search_verif.v`](theories/binary_search_verif.v): Contract for the
  C program following the [Java specification][java-specification-url] and a Coq proof using the
  [Verified Software Toolchain][vst-url] that the program upholds the contract.

### General configuration

- [`coq-program-verification-template.opam`](coq-program-verification-template.opam):
  Project [OPAM package][opam-url] definition, including dependencies.
- [`_CoqProject`](_CoqProject): File used by Coq IDEs to determine the Coq logical path,
  and by the Make-based build to obtain the list of files to include. 
- [`.github/workflows/coq-ci.yml`](.github/workflows/coq-ci.yml): [GitHub Actions][github-actions-ci-url]
  continuous integration configuration for Coq, using the OPAM package definition.

### Make configuration

- [`Makefile`](Makefile): Generic delegating makefile using [coq_makefile][coq-makefile-url].
- [`Makefile.coq.local`](Makefile.coq.local): Custom optional Make tasks, including compilation
  of the C program.

### Dune configuration

- [`dune-project`](dune-project): General configuration for the [Dune][dune-url] build system.
- [`theories/dune`](theories/dune): Dune build configuration for Coq.

## Caveats

### coq_makefile vs. Dune

coq_makefile and Dune builds are independent. However, for local development,
it is recommended to use coq_makefile, since Coq IDEs may not be able find
files compiled by Dune. Due to its build hygiene requirements, Dune will
refuse to build when compiled (`.vo`) files are present in `theories`;
run `make clean` to remove them.

### Generating Clight for Coq

The Coq representation of the C program (`binary_search.v`) is kept in version
control due to licensing concerns for CompCert's `clightgen` tool.
If you have a license to use `clightgen`, you can delete the generated file
and have the build system regenerate it. To regenerate the file manually, you need to run:
```shell
clightgen -o theories/binary_search.v -normalize src/binary_search.c
```

[binary-search-url]: http://ai.googleblog.com/2006/06/extra-extra-read-all-about-it-nearly.html
[java-specification-url]: https://hg.openjdk.java.net/jdk10/jdk10/jdk/file/ffa11326afd5/src/java.base/share/classes/java/util/Arrays.java#l1846
[vst-url]: https://vst.cs.princeton.edu
[compcert-c-url]: http://compcert.inria.fr/compcert-C.html
[coq-makefile-url]: https://coq.inria.fr/refman/practical-tools/utilities.html#building-a-coq-project-with-coq-makefile
[github-actions-ci-url]: https://github.com/coq-community/docker-coq-action
[opam-url]: https://opam.ocaml.org
[dune-url]: https://dune.build
