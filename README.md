# checkProofs

This is the project containing bachelor thesis AIM'26 HSE SPB
Main goal:
Creating application for verifying proofs in equational reasoning style in Haskell

---

## Features

- This project is runned by Cabal
- To process default file [AllGoodExamples.hs](examples/AllGoodExamples.hs) or pass your own to arguments
- File [src\ProofBase.hs](src/ProofBase.hs) contains description of annotation language and 

---

## Basic defenitions

For implementation puorposes all the function defenitions should be consistent. We use [haskell report 2010](https://www.haskell.org/onlinereport/haskell2010/)

- To succesfully execute you own module please use provided annotation options and use module [src/ProofBase.hs](src/ProofBase.hs)
``` bash
ghc <file path> <path to the repo>/src/ProofBase.hs
```
- To process default file [AllGoodExamples.hs](examples/AllGoodExamples.hs) or pass your own to arguments

---

## Experiments

- GHC = 9.12.2
- Cabal = 3.14.2.0
- Directory examples contains number of theorems with proofs to run experiments. Incuding
    * Instances for class types Functor, Applicative and Monad for basic types like: Maybe, Either, Arrow (->)
    * Theorems of Monad equality to AltMonad defenition
    * Prooves of liftM and liftA is fmap

---

## Build

``` bash
cabal run
```
or

``` bash
cabal run checkProofs -- <file path>
```

---

## Haddock
run
``` bash
cabal haddock --haddock-executables
```
to create fresh Haddock or you can look into [papers\haddock-21052026](papers/haddock-21052026) to see version for thesis

---

## Papers

You can check final version of thesis paper in russian language

---
Arina Ivanova
