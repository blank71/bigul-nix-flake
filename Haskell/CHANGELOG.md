1.0.0 Changes
=============

Version 1.0.0 is the first official release, and is *not* compatible with
0.9.0 and earlier development versions.

The targeted GHC version is 7.10; 8.0 support is postponed due to its
non–backward compatible revisions to Template Haskell.

* Module restructuring

  The module structure is refined and simplified, with `Generics.BiGUL.AST`
  changed to `Generics.BiGUL`, pattern matching functions extracted to
  `Generics.BiGUL.PatternMatching`, and `Generics.BiGUL.Lib` created to
  serve as a prelude. More specific library modules are placed under
  `Generics.BiGUL.Lib.`:

  - `Generics.BiGUL.Lib.List` is the place for list-processing library
    programs. For now the only inhabitant is the “BiFluX alignment”.

  - `Generics.BiGUL.Lib.HuStudies` contains some small, concrete examples
    illustrating the use of every BiGUL construct.

* Major changes to `Generics.BiGUL.TH`

  - `deriveBiGULGeneric` now supports `newtype`.

  - The `update` syntax now takes the source pattern as its first argument
    and the view pattern as its second argument. (Previously the view
    pattern comes first.)

  - `rearrV` and `update` now check at compile time whether all view
    information is used (forbidding wildcard in view patterns and requiring
    all view variables are used); also `rearrS` and `rearrV` check whether
    their first argument is a one-argument lambda-expression.

  - The branch construction syntax has been slimmed down to just four
    functions: `normal`, `normalSV`, `adaptive`, and `adaptiveSV`.

  - Normal branch constructing functions now take an additional argument
    specifying on the source an “exit condition”, which should be satisfied
    by the updated source after the branch body is executed. All the exit
    conditions in a `Case` statement should (ideally) be disjoint.
    Overlapping exit conditions are still allowed for fast prototyping,
    though — the putback semantics of 'Case' will compute successfully as
    long as the ranges of the branches are disjoint (regardless of whether
    the exit conditions are specified precisely enough).

* Error-reporting mechanism overhauled

  - The types of `put` and `get` from `Generics.BiGUL.Interpreter` are
    changed to produce simply `Maybe` results. When execution fails
    (producing `Nothing`), invoke `putTrace` and `getTrace` to see the
    exact failure and the execution trace leading to the failure.

  - The execution traces include intermediate sources and views; the types
    used in a BiGUL program are thus required to be instances of `Show`.

* Show instances for BiGUL programs removed

  There are two reasons: Functions, which are everywhere in BiGUL programs,
  cannot be shown; and worse, printing of recursive BiGUL programs will not
  terminate.
