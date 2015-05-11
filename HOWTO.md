# How to build CVC4 in proof production mode (under Linux)

- Download the sources

- In the `contrib` directory:
```
./get-antlr-3.4
```

- In the main directory:
```
./configure --with-antlr-dir=$PATH_TO_CVC4/antlr-3.4
ANTLR=$PATH_TO_CVC4/antlr-3.4/bin/antlr3 --enable-proof
--enable-static-binary --with-cln --with-build=production

make
```

- To run CVC4:
```
cvc4 foo.smt2 --proof --dump-proofs [--check-proofs]
```
