# Coq Program Verification Template

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/palmskog/coq-program-verification-template/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/palmskog/coq-program-verification-template/actions?query=workflow:"Docker%20CI"

Template project for program verification in Coq.
Uses the Verified Software Toolchain and a classic binary
search program in C as an example.

## Meta

- Author(s):
  - Karl Palmskog
- License: [Unlicense](LICENSE)
- Compatible Coq versions: 8.14 or later
- Additional dependencies:
  - [CompCert](http://compcert.inria.fr) 3.12 or later
  - [Verified Software Toolchain](https://vst.cs.princeton.edu) 2.12 or later
- Coq namespace: `ProgramVerificationTemplate`

## Building instructions

### Installing dependencies

The recommended way to install Coq and other dependencies is via
[opam](https://opam.ocaml.org/doc/Install.html), for example:
```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.16.1 coq-compcert.3.12 coq-vst.2.12
```

### Obtaining the project

```shell
git clone https://github.com/palmskog/coq-program-verification-template.git
cd coq-program-verification-template
```

### Option 1: building the project using coq_makefile

With make and the [coq_makefile tool][coq-makefile-url] bundled with Coq:
```shell
make   # or make -j <number-of-cores-on-your-machine> 
```

### Option 2: building the project using Dune

With the [Dune build system][dune-url], version 3.8.1 or later:
```shell
dune build
```

### Compiling the program using CompCert (optional)

```shell
ccomp -o bsearch src/binary_search.c
```

## File and directory structure

### Core files

- [`src/binary_search.c`](src/binary_search.c): C program that performs binary
  search in a sorted array, inspired by [Joshua Bloch's Java version][binary-search-url].
- [`theories/binary_search.v`](theories/binary_search.v): Coq representation
  of the binary search C program in [CompCert's Clight language][compcert-c-url].
- [`theories/binary_search_theory.v`](theories/binary_search_theory.v): General
  Coq definitions and facts relevant to binary search, adapted from code in the
  [Verified Software Toolchain][vst-url].
- [`theories/binary_search_verif.v`](theories/binary_search_verif.v): Contract for the
  Clight program following the [Java specification][java-specification-url] and a
  Coq proof using the Verified Software Toolchain that the program upholds the contract.

### General configuration

- [`coq-program-verification-template.opam`](coq-program-verification-template.opam):
  Project [opam package][opam-url] definition, including dependencies.
- [`_CoqProject`](_CoqProject): File used by Coq editors to determine the Coq logical path,
  and by the make-based build to obtain the list of files to include. 
- [`.github/workflows/docker-action.yml`](.github/workflows/docker-action.yml):
  [GitHub Actions][github-actions-ci-url] continuous integration configuration for Coq,
  using the opam package definition.

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
it is recommended to use coq_makefile, since Coq editors may not be able find
files compiled by Dune. Due to its build hygiene requirements, Dune will
refuse to build when binary (`.vo`) files are present in `theories`;
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
[compcert-c-url]: https://compcert.org/compcert-C.html
[coq-makefile-url]: https://coq.inria.fr/refman/practical-tools/utilities.html#building-a-coq-project-with-coq-makefile
[github-actions-ci-url]: https://github.com/coq-community/docker-coq-action
[opam-url]: https://opam.ocaml.org
[dune-url]: https://dune.build
