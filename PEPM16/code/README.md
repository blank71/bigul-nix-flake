# BiGUL: A formally verified core language for putback-based bidirectional programming

This is the Agda source for the paper with the above title appearing in _Partial Evaluation and Program Manipulation_ 2016 (doi: [10.1145/2847538.2847544](http://dx.doi.org/10.1145/2847538.2847544)).

All files have been typechecked with Agda version 2.4.2.4 and Standard Library version 0.11.

A hyperlinked HTML version of the code is under the directory `html`. (All BiGUL modules are listed in `html/BiGUL.Everything.html`.)

See [the BiGUL project homepage](http://www.prg.nii.ac.jp/project/bigul/) for more information.
## Module descriptions

#### BiGUL.BiGUL
Definitions of BiGUL and its interpreter.

#### BiGUL.Bookstore
The bookstore example (Figure 2).

#### BiGUL.CaseExamples
Small examples for caseS and caseV in Sections 3.4.2 and 3.5.

#### BiGUL.CompSeq
A simplified version of the monad reification trick presented in Section 2.

#### BiGUL.Lens
Basic definitions of lenses and the uniqueness lemma (put uniquely determines get).

#### BiGUL.ListAlignment
List alignment (Section 3.6).

#### BiGUL.Partiality
The Par datatype, which reifies the Maybe monad, and types of proofs of successful or failed computation (Section 2.1).

#### BiGUL.SourceCase
Source case analysis (Section 3.4).

#### BiGUL.TransatlanticCorporation
The transatlantic corporation example (Section 4).

#### BiGUL.Universe
A universe of mutually inductive datatypes and patterns for them (Section 3.2).

#### BiGUL.Utilities
Some auxiliary definitions.

#### BiGUL.ViewCase
View case analysis (Section 3.5).

#### BiGUL.ViewRearrangement
View rearrangement (Section 3.3).
