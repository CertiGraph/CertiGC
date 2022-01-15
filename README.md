# CertiGC

A formally verified garbage collector, implemented in `C` and proven correct in [Coq](https://coq.inria.fr/).

Built on [CertiGraph](https://github.com/Salamari/CertiGraph/).

## Contributors

* [Aquinas Hobor](https://github.com/Salamari/)
* [Shengyi Wang](https://github.com/txyyss/)
* [Anshuman Mohan](https://github.com/anshumanmohan/)
* [Tim Carstens](https://github.com/intoverflow/)

## Install the dependencies

Clone and install [CertiGraph](https://github.com/Salamari/CertiGraph/) using the included `opam` files.

## Install

Two `opam` files are provided: one for `x86_64-linux`, the other for `x86_32-linux`. They can be installed side-by-side:

```console
$ opam install ./coq-certigc.opam ./coq-certigc-32.opam
```

## Build without installing (64-bit)

```console
$ make all
```

## Build without installing (32-bit)

```console
$ make deepclean ; make BITSIZE=32 all
```
