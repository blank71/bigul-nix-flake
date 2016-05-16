1.0.0 Changes
=============

Version 1.0.0 is the first feature-complete release, and is *not*
compatible with 0.9.0 and earlier development versions.

+ Module restructuring

  The module structure is refined and simplified, with `Generics.BiGUL.AST`
  changed to `Generics.BiGUL`, pattern matching functions extracted to
  `Generics.BiGUL.PatternMatching`, and `Generics.BiGUL.Lib` created to
  serve as a prelude. More specific library modules can be placed under
  `Generics.BiGUL.Lib`, like `Generics.BiGUL.Lib.List`.

+ Show instances for BiGUL programs removed

  There are two reasons: Functions, which are everywhere in BiGUL programs,
  cannot be shown; and worse, printing of recursive BiGUL programs will not
  terminate.

+ KindSignatures no longer needed
