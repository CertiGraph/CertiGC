# CertiGC

[![build](https://github.com/intoverflow/CertiGC/actions/workflows/build.yml/badge.svg)](https://github.com/intoverflow/CertiGC/actions/workflows/build.yml)

![GitHub](https://img.shields.io/github/license/intoverflow/CertiGC)

A [Verified Software Unit](https://github.com/appliedfm/coq-vsu) that provides a formally verified generational garbage collector.

Implemented in C, modeled in [Coq](https://coq.inria.fr), and proven correct using the [Verified Software Toolchain](https://vst.cs.princeton.edu/) and [CertiGraph](https://github.com/Salamari/CertiGraph/).

Compatible with [CompCert](https://compcert.org/).


## Verification status

Specifications are proven correct for the following targets:

- [x] `x86_64-linux`
- [ ] `x86_32-linux`

Proofs are checked by our [CI infrastructure](https://github.com/intoverflow/CertiGC/actions/workflows/build.yml).

## Contributors

* [Aquinas Hobor](https://github.com/Salamari/)
* [Shengyi Wang](https://github.com/txyyss/)
* [Anshuman Mohan](https://github.com/anshumanmohan/)
* [Tim Carstens](https://github.com/intoverflow/)

## Install the dependencies

Clone and install [CertiGraph](https://github.com/Salamari/CertiGraph/) using the included `opam` files.


## Packages

* `coq-vsu-gc-src` - C source code
* `coq-vsu-gc-vst` - VST model, spec, and proof (`x86_64-linux`)
* `coq-vsu-gc-vst-32` - VST model, spec, and proof (`x86_32-linux`)
* `coq-vsu-gc` - All of the above

## Installing

Installation is performed by `opam` with help by [coq-vsu](https://github.com/appliedfm/coq-vsu).

```console
$ opam pin -n -y .
$ opam install --working-dir ./coq-vsu-gc.opam
```

## Using the C library

The C library is installed to the path given by `vsu -I`. For example:

```console
$ tree `vsu -I`
/home/tcarstens/.opam/coq-8.14/lib/coq-vsu/lib/include
└── coq-vsu-gc
    ├── gc.h
    └── src
        └── gc.c

2 directories, 2 files
$
```

## Building without `opam`

The general pattern looks like this:

```console
$ make [verydeepclean|deepclean|clean]
$ make BITSIZE={opam|64|32} [all|_CoqProject|clightgen|theories]
```

`BITSIZE` determines which `compcert` target to use. If unspecified, the default value is `opam`:

* `opam` and `64` both use `x86_64-linux`
* `32` uses `x86_32-linux`

### Example: `x86_64-linux`

```console
$ make verydeepclean ; make
```

### Example: `x86_32-linux`

```console
$ make verydeepclean ; make BITSIZE=32
```

#

[![Coq](https://img.shields.io/badge/-Coq-royalblue)](https://github.com/coq/coq)
[![compcert](https://img.shields.io/badge/-compcert-pink)](https://compcert.org/)
[![VST](https://img.shields.io/badge/-VST-palevioletred)](https://vst.cs.princeton.edu/)
