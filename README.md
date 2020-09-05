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

It is recommended to install Coq and other dependencies via
[OPAM](https://opam.ocaml.org/doc/Install.html), for example:
```shell
opam install coq.8.12.0 coq-vst.2.6 coq-compcert
```

### Obtaining the project

```shell
git clone https://github.com/palmskog/coq-program-verification-template.git
cd coq-program-verification-template
```

### Building the project using Make

```shell
make   # or make -j <number-of-cores-on-your-machine> 
```

### Building the project using Dune

``` shell
dune build
```

### Compile the program using CompCert (optional)

```shell
ccomp -o bsearch src/binary_search.c
```

## File and directory structure

### Core files

- [`src/binary_search.c`](src/binary_search.c): C program that performs binary
  search in a sorted array, adapted from [Joshua Bloch's Java version][binary-search-url].
- [`theories/binary_search.v`](theories/binary_search.v): Coq representation
  of the binary search C program in [CompCert's C variant][compcert-c-url].
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

- [`dune-project`](dune-project): Dune general configuration.
- [`theories/dune`](theories/dune): Dune Coq build configuration.

## Caveats

- Make and Dune builds are independent; either can be used to build
  the project. However, for local development, it is recommended to use Make,
  since Coq IDEs may not be able find files compiled by Dune.
- The Coq representation of the C program is kept in version control due
  to licensing concerns for CompCert's `clightgen` tool.

[binary-search-url]: http://ai.googleblog.com/2006/06/extra-extra-read-all-about-it-nearly.html
[java-specification-url]: https://hg.openjdk.java.net/jdk10/jdk10/jdk/file/ffa11326afd5/src/java.base/share/classes/java/util/Arrays.java#l1846
[vst-url]: https://vst.cs.princeton.edu
[compcert-c-url]: http://compcert.inria.fr/compcert-C.html
[coq-makefile-url]: https://coq.inria.fr/refman/practical-tools/utilities.html#building-a-coq-project-with-coq-makefile
[github-actions-ci-url]: https://github.com/coq-community/docker-coq-action
[opam-url]: https://opam.ocaml.org
