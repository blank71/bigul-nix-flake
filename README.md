# BiGUL: The Bidirectional Generic Update Language #

Putback-based bidirectional programming allows the programmer to write only one putback transformation, from which the unique corresponding forward transformation is derived for free. BiGUL, short for the Bidirectional Generic Update Language, is designed to be a minimalist putback-based bidirectional programming language. Originally developed in the dependently typed programming language [Agda](http://wiki.portal.chalmers.se/agda/pmwiki.php), BiGUL’s well-behavedness has been completely formally verified. It has subsequently been ported to [Haskell](https://www.haskell.org) for developing various bidirectional applications.

The module `Generics.BiGUL.Lib.HuStudies` ([haddock documentation on Hackage](https://hackage.haskell.org/package/BiGUL/docs/Generics-BiGUL-Lib-HuStudies.html)) contains some small, illustrative examples of BiGUL programs, and is a good place for getting started quickly.

For more detail, see the following:

* Hsiang-Shang Ko, Tao Zan, and Zhenjiang Hu. BiGUL: A formally verified core language for putback-based bidirectional programming. In [_Partial Evaluation and Program Manipulation_](http://conf.researchr.org/home/pepm-2016), PEPM’16, pages 61–72. ACM, 2016. http://dx.doi.org/10.1145/2847538.2847544.
* Zhenjiang Hu and Hsiang-Shang Ko. Principle and Practice of Bidirectional Programming in BiGUL. (Draft manuscript for the [_Oxford Summer School on Bidirectional Transformations_](https://www.cs.ox.ac.uk/projects/tlcbx/ssbx/).) https://bitbucket.org/prl_tokyo/bigul/raw/master/SummerSchool16/paper/BiGUL_tutorial.pdf.

## Installation ##

BiGUL works with [GHC](https://www.haskell.org/ghc/) 7.10 and above, and is released to [Hackage](https://hackage.haskell.org/package/BiGUL), so the installation of the latest release of BiGUL is as simple as executing
```
cabal update
cabal install BiGUL
```
in the command line (i.e., the standard way of installing Haskell packages).

The most recent development version (with changes not yet released to Hackage) is maintained in the `master` branch. To install the development version, first clone this git repository, and then invoke `cabal install` under the `Haskell/` subdirectory of the local copy of the repository:
```
git clone https://bitbucket.org/prl_tokyo/BiGUL.git
cd BiGUL/Haskell/
cabal update
cabal install
```
