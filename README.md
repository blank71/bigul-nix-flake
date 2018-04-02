# BiGUL: The Bidirectional Generic Update Language #

Putback-based bidirectional programming allows the programmer to write only one putback transformation, from which the unique corresponding forward transformation is derived for free. BiGUL, short for the Bidirectional Generic Update Language, is designed to be a minimalist putback-based bidirectional programming language. Originally developed in the dependently typed programming language [Agda](http://wiki.portal.chalmers.se/agda/pmwiki.php), BiGUL’s well-behavedness has been completely formally verified. It has subsequently been ported to [Haskell](https://www.haskell.org) for developing various bidirectional applications.

The module `Generics.BiGUL.Lib.HuStudies` ([haddock documentation on Hackage](https://hackage.haskell.org/package/BiGUL/docs/Generics-BiGUL-Lib-HuStudies.html)) contains some small, illustrative examples of BiGUL programs, and is a good place for getting started quickly.

Recommended (especially to mathematically inclined programmers) is a semi-formal introduction to BiGUL programming in terms of an axiomatic semantics, which clarifies the reasoning required for writing correct BiGUL programs:

* Hsiang-Shang Ko and Zhenjiang Hu. An Axiomatic Basis for Bidirectional Programming. _Proceedings of the ACM on Programming Languages_, 2(POPL):41, 2018. https://doi.org/10.1145/3158129. (PDF download: https://dl.acm.org/ft_gateway.cfm?id=3158129.)

There is a less theory-oriented tutorial, which gives a taste of programming with the Haskell port of BiGUL and its implementation:

* Zhenjiang Hu and Hsiang-Shang Ko. Principles and Practice of Bidirectional Programming in BiGUL. In [_International Summer School on Bidirectional Transformations (Oxford, UK, 25–29 July 2016)_](https://www.cs.ox.ac.uk/projects/tlcbx/ssbx/), volume 9715 of _Lecture Notes in Computer Science_, chapter 4, pages 100–150. Springer, 2018. https://doi.org/10.1007/978-3-319-79108-1_4. (A preprint of the chapter is available at https://bitbucket.org/prl_tokyo/bigul/raw/master/SSBX16/tutorial.pdf.)

An earlier paper describes the reification technique used in the Agda formalisation; this paper uses an outdated version of BiGUL, but the reification technique still underlies the current formalisation.

* Hsiang-Shang Ko, Tao Zan, and Zhenjiang Hu. BiGUL: A formally verified core language for putback-based bidirectional programming. In [_Partial Evaluation and Program Manipulation_](http://conf.researchr.org/home/pepm-2016), PEPM’16, pages 61–72. ACM, 2016. https://doi.org/10.1145/2847538.2847544. ([The first author’s personal website](https://josh-hs-ko.github.io/#publication-c48b059c) contains an _ACM Author-Izer_ link for downloading the paper for free.)

## Installation ##

BiGUL works with [GHC](https://www.haskell.org/ghc/) 7.10 and 8.0 (and possibly above — see below), and is released to [Hackage](https://hackage.haskell.org/package/BiGUL), so the installation of the latest release of BiGUL is as simple as executing
```
cabal update
cabal install BiGUL
```
in the command line (i.e., the standard way of installing Haskell packages).

For newer versions of GHC, you may see some `cabal` error messages like the following, which complains about the version of `base`:
```
...
cabal: Could not resolve dependencies:
trying: BiGUL-1.0.1 (user goal)
next goal: base (dependency of BiGUL-1.0.1)
rejecting: base-4.10.1.0/installed-4.1... (conflict: BiGUL => base==4.9.*)
...
```
In this case, try to execute
```
cabal install BiGUL --allow-newer=base
```
instead. If there are no major changes to the API of GHC, BiGUL should still compile.

The most recent development version (with changes not yet released to Hackage) is maintained in the `master` branch. To install the development version, first clone this git repository, and then invoke `cabal install` under the `Haskell/` subdirectory of the local copy of the repository:
```
git clone https://bitbucket.org/prl_tokyo/BiGUL.git
cd BiGUL/Haskell/
cabal update
cabal install
```