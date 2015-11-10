# BiGUL Installation

In the terminal, as a normal user, run:

```sh
cabal configure
cabal build
cabal install
```

This installs the library and also the examples as executables.

## Loading the Test/Test.hs file into GHCi

```sh
cabal repl test
```

# Simple Explanation

## Lang.AST
  
  All BiGUL language constructors.

## Lang.Interpreter

  Two functions: `put` and `get`.

## Lang.MonadBiGULError

## Usage
 
   use `import Generics.BiGUL`.