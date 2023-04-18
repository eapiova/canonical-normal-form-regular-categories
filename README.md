A partially formalised proof of the canonical-form theorem for the dependent type theory of the regular categories. The formalisation is built on top of the [General Type Theories framework](https://github.com/peterlefanulumsdaine/general-type-theories).

# Installation

It is recommended to use the opam package manager to install the environment. Details about installing Opam can be found [here](https://opam.ocaml.org/doc/Install.html).

1. Install Coq
```
$ opam install coq
```
2. Add the released coq-archive packages:

```
$ opam repo add coq-released https://coq.inria.fr/opam/released
```
3. Install Coq-HoTT

```
$ opam install coq-hott
```

4. Generate a makefile from _CoqProject with 

```
$ coq_makefile -f _CoqProject -o CoqMakefile
```

5. Compile the project with 
```
$ make -f CoqMakefile
```

6. Use CoqIDE (shipped with Coq), [VSCoq](https://github.com/coq-community/vscoq) or [ProofGeneral](https://proofgeneral.github.io/)

# Contents





