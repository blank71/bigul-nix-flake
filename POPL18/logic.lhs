%% For double-blind review submission
%\documentclass[acmsmall,10pt,fleqn,review,anonymous]{acmart}\settopmatter{printfolios=true}
%% For single-blind review submission
%\documentclass[acmsmall,10pt,fleqn,review]{acmart}\settopmatter{printfolios=true}
%% For final camera-ready submission
\documentclass[acmsmall,10pt,fleqn,screen]{acmart}\settopmatter{}

%% Note: Authors migrating a paper from PACMPL format to traditional
%% SIGPLAN proceedings format should change 'acmlarge' to
%% 'sigplan,10pt'.

%include polycode.fmt

\newcommand{\keyword}[1]{\mathbf{#1}}
\newcommand{\identifier}[1]{\mathit{#1}}
\makeatletter
\newcommand{\shorteq}{%
  \settowidth{\@@tempdima}{-}%
  \resizebox{\@@tempdima}{\height}{=}%
}
\makeatother
\definecolor{indent}{gray}{.6}
\newcommand{\idots}{\kern.25pt\vphantom{||}{\color{indent}\smash{\rlap{\rule[13pt/4*2+.25pt]{1pt}{1pt}}\rlap{\rule[13pt/4*1+.25pt]{1pt}{1pt}}\rlap{\rule[13pt/4*0+.25pt]{1pt}{1pt}}\rlap{\rule[13pt/4*(-1)+.25pt]{1pt}{1pt}}}}\kern-.25pt\quad}

%format of = "\keyword{of}"
%format if = "\keyword{if}"
%format then = "\keyword{then}"
%format else = "\keyword{else}"
%format = = "{=}"
%format -> = "{\to}"
%format => = "{\Rightarrow}"
%format <== = "{\Leftarrow}"
%format | = "{|}"
%format == = "{\shorteq\kern.5pt\shorteq}"
%format /= = "{\neq}"
%format <= = "{\leq}"
%format >= = "{\geq}"
%format && = "{\wedge}"
%format || = "{\vee}"
%format : = "{:}"
%format `elem` = "{\in}"
%format . = "{\circ}"
%format !! = "\kern-1pt{!\kern-.75pt!}\kern-1pt"
%format / = "\kern-\smallskipamount{/}\kern-1.5\smallskipamount"
%format Nat = "\mathbb{N}"
%format Int = "\mathbb{Z}"
%format Rational = "\mathbb{Q}"
%format ~ = " "
%format ... = "\ldots"
%format VDOTS = "\kern.6em\vphantom{|}\smash{\raisebox{-2pt}{\vdots}}"
%format ^ = "\idots"

%format _, = _ "\kern1.5pt" ,
%format b, = b "\kern1pt" ,
%format l, = l "\kern1pt" ,
%format n, = n "\kern1pt" ,
%format s, = s "\kern1pt" ,
%format v, = v "\kern1pt" ,
%format w, = w "\kern1pt" ,
%format x, = x "\kern1pt" ,

%format (all(x)) = "\forall" x "."
%format (some(x)) = "\exists" x "."
%format EMPTY = "\emptyset"
%format <~ = "{\hookleftarrow}"
%format LUB = "{\textstyle\bigsqcup}\kern-\smallskipamount"
%format BIGCUP = "{\textstyle\bigcup}\kern-\smallskipamount"
%format (POWER x) = "\mathcal P" x
%format SUBSETEQ = "{\subseteq}"
%format CAP = "{\cap}"
%format CUP = "{\cup}"
%format (GRAPH x) = "{\mathcal G}" x
%format TIMES = "{\times}"
%format (VEC(x)) = "\vec{" x "}"
%format (NORM(x)) = "\widehat{" x "}"
%format INNER = "\raisebox{.75pt}{\scalebox{.75}{\rotatebox[origin=c]{180}{\ensuremath{\Lsh}}}}"
%format OR = "\kern-1.25\smallskipamount/\kern-1.25\smallskipamount"
%format Domain = "\mathcal D"
%format NormalDomain = "\mathcal N"
%format CaseRange = "\mathcal P^\prime"
%format Reentry = "\mathcal F\kern-1pt"
%format Postcondition = "\mathcal F^\prime"
%format (STAR x) = x "\kern1pt^\star"
%format (SUB(x)(y)) = "{" x "}_{" y "}"
%format ss'' = "\widetilde{ss}"
%format s'' = "\tilde{s}"
%format Pat = "\mathsf{Pat}"
%format Branch = "\mathsf{Branch}"
%format (SEQ x) = x "^*"

%format fail = "\keyword{fail}"
%format skip = "\keyword{skip}"
%format replace = "\keyword{replace}"
%format rearrS = "\keyword{rearrS}"
%format rearrV = "\keyword{rearrV}"
%format case = "\keyword{case}"
%format normal = "\keyword{normal}"
%format exit = "\keyword{exit}"
%format exit' = "\identifier{exit}"
%format adaptive = "\keyword{adaptive}"

%format zero = "\mathsf{zero}"
%format suc = "\mathsf{suc}"

%format 0 = "\mathrm 0"
%format 1 = "\mathrm 1"
%format 2 = "\mathrm 2"
%format 3 = "\mathrm 3"
%format 4 = "\mathrm 4"
%format 5 = "\mathrm 5"
%format 6 = "\mathrm 6"
%format 7 = "\mathrm 7"
%format 8 = "\mathrm 8"
%format 9 = "\mathrm 9"

%format *1 = "\mathbf 1"
%format *2 = "\mathbf 2"
%format *3 = "\mathbf 3"
%format *4 = "\mathbf 4"
%format *5 = "\mathbf 5"
%format *6 = "\mathbf 6"
%format *7 = "\mathbf 7"
%format *8 = "\mathbf 8"
%format *9 = "\mathbf 9"

\definecolor{putback}{RGB}{60,116,219}
\definecolor{range}{RGB}{0,140,0}

\newcommand{\assert}[1]{{\color{putback}\{}\,#1\,{\color{putback}\}}}
\newcommand{\assertl}[1]{{\color{putback}\{}\,#1}
\newcommand{\assertr}[1]{\qquad #1\,{\color{putback}\}}}
\newcommand{\varassert}[2]{{\color{putback}\{\,#1\kern-\smallskipamount:}\,\ #2\,{\color{putback}\}}}
\newcommand{\varassertl}[2]{{\color{putback}\{\,#1\kern-\smallskipamount:}\,\ #2}
\newcommand{\assertrange}[1]{{\color{range}\{\!\{}\,#1\,{\color{range}\}\!\}}}
\newcommand{\varassertrange}[2]{{\color{range}\{\!\{\,#1\kern-\smallskipamount:}\,\ #2\,{\color{range}\}\!\}}}

%format (ENV(x)) = "\overline{" x "}"
%format (COM(x)) = "\langle\," x "\,\rangle"
%format (ASSERT(x)) = "\assert{" x "}"
%format (ASSERTL(x)) = "\assertl{" x "}"
%format (ASSERTR(x)) = "\assertr{" x "}"
%format (ASSERT'(y)(x)) = "\varassert{" y "}{" x "}"
%format (ASSERTL'(y)(x)) = "\varassertl{" y "}{" x "}"
%format (ASSERTRANGE(x)) = "\assertrange{" x "}"
%format (ASSERTRANGE'(y)(x)) = "\varassertrange{" y "}{" x "}"
%format (ASSERTNUMBER(x)) = "\kern-\smallskipamount_{\color{putback}" x "}"
%format (ASSERTRANGENUMBER(x)) = "\kern-\smallskipamount_{\color{range}" x "}"

\newcommand{\name}[1]{\textsc{#1}}
\newcommand{\BiGUL}{\name{BiGUL}}
\newcommand{\Agda}{\name{Agda}}
\newcommand{\Haskell}{\name{Haskell}}
\newcommand{\PutGet}{\name{PutGet}}
\newcommand{\GetPut}{\name{GetPut}}
\newcommand{\PutTwice}{\name{PutTwice}}
\newcommand{\PutbackRecursion}{\name{PutbackRecursion}}\newcommand{\RangeRecursion}{\name{RangeRecursion}}

\usepackage{xifthen}

\newcommand{\reason}[1]{\quad\{\text{-~#1~-}\}}
\newcommand{\varcitet}[3][]{\citeauthor{#2}#3~[\ifthenelse{\isempty{#1}}{\citeyear{#2}}{\citeyear[#1]{#2}}]}
\newcommand{\awa}[2]{\mathrlap{#2}\phantom{#1}} % as wide as
\newcommand{\varawa}[2]{\phantom{#1}\mathllap{#2}}
\newcommand{\IF}{\text{If}\quad}
\newcommand{\AND}{\quad\text{and}\quad}
\newcommand{\THEN}{\quad\text{then}\quad}
\newcommand{\IFF}{\quad\text{if and only if}\quad}
\newcommand{\PERIOD}{\quad\text{.}}
\newcommand{\rulepsep}{\hspace{1em}}
\newcommand{\rulehsep}{\hspace{.5em}}
\newcommand{\rulevsep}{\vspace{1.5ex}}
\newcommand{\adjustrearr}{\vrule height 9.5pt width 0pt}
\newcommand{\adjustrearrmore}{\vrule height 10pt width 0pt}
\newcommand{\adjustnorm}{\vrule height 11pt width 0pt}

%% Some recommended packages.
\usepackage{booktabs}   %% For formal tables:
                        %% http://ctan.org/pkg/booktabs
\usepackage{subcaption} %% For complex figures with subfigures/subcaptions
                        %% http://ctan.org/pkg/subcaption

\usepackage{mathtools}
\usepackage{enumitem}
\usepackage[UKenglish]{isodate}

\usepackage[color=yellow,textsize=footnotesize]{todonotes}
\setlength{\marginparwidth}{2cm}

\renewcommand{\sectionautorefname}{Section}
\renewcommand{\subsectionautorefname}{Section}
\renewcommand{\subsubsectionautorefname}{Section}
\renewcommand{\figureautorefname}{Figure}
\newcommand{\lemmaautorefname}{Lemma}
\newcommand{\propositionautorefname}{Proposition}
\newcommand{\corollaryautorefname}{Corollary}
\newcommand{\definitionautorefname}{Definition}
\newcommand{\exampleautorefname}{Example}
\newcommand{\notationautorefname}{Notation}

\newcommand{\varparagraph}[1]{\paragraph{#1}\hspace{.5em}} %{\vspace{1ex plus .1ex minus .1ex}\textit{#1}\hspace{.5em}}

\makeatletter\if@@ACM@@journal\makeatother
%% Journal information (used by PACMPL format)
%% Supplied to authors by publisher for camera-ready submission
\acmJournal{PACMPL}
\acmYear{2018}
\acmVolume{2}
\acmNumber{POPL}
\acmArticle{41}
\acmMonth{1}
\acmPrice{}
\acmDOI{10.1145/3158129}
%\startPage{1}
%\else\makeatother
%% Conference information (used by SIGPLAN proceedings format)
%% Supplied to authors by publisher for camera-ready submission
%\acmConference[POPL'18]{ACM SIGPLAN Symposium on Principles of Programming Languages}{January 10--12, 2018}{Los Angeles, CA, USA}
%\acmYear{2018}
%\acmISBN{978-x-xxxx-xxxx-x/YY/MM}
%\acmDOI{10.1145/nnnnnnn.nnnnnnn}
%\startPage{1}
\fi


%% Copyright information
%% Supplied to authors (based on authors' rights management selection;
%% see authors.acm.org) by publisher for camera-ready submission
%\setcopyright{none}             %% For review submission
%\setcopyright{acmcopyright}
%\setcopyright{acmlicensed}
\setcopyright{rightsretained}
%\copyrightyear{2017}           %% If different from \acmYear


%% Bibliography style
\bibliographystyle{ACM-Reference-Format}
%% Citation style
%% Note: author/year citations are required for papers published as an
%% issue of PACMPL.
\citestyle{acmauthoryear}   %% For author/year citations
\setcitestyle{nosort}

\begin{document}

\setlength{\mathindent}{\parindent}

%% Title information
\title{An Axiomatic Basis for Bidirectional Programming}
                                        %% [Short Title] is optional;
                                        %% when present, will be used in
                                        %% header instead of Full Title.
%\begin{anonsuppress}
%\titlenote{Draft manuscript (\today)}   %% \titlenote is optional;
%\end{anonsuppress}
                                        %% can be repeated if necessary;
                                        %% contents suppressed with 'anonymous'
%\subtitle{Subtitle}                    %% \subtitle is optional
%\subtitlenote{with subtitle note}      %% \subtitlenote is optional;
                                        %% can be repeated if necessary;
                                        %% contents suppressed with 'anonymous'


%% Author information
%% Contents and number of authors suppressed with 'anonymous'.
%% Each author should be introduced by \author, followed by
%% \authornote (optional), \orcid (optional), \affiliation, and
%% \email.
%% An author may have multiple affiliations and/or emails; repeat the
%% appropriate command.
%% Many elements are not rendered, but should be provided for metadata
%% extraction tools.

%% Author with single affiliation.
\author{Hsiang-Shang Ko}
%\authornote{with author1 note}         %% \authornote is optional;
                                        %% can be repeated if necessary
%\orcid{nnnn-nnnn-nnnn-nnnn}            %% \orcid is optional
\affiliation{
  \position{Assistant Professor by Special Appointment}
  \institution{National Institute of Informatics}
                                        %% \institution is required
%  \department{Information Systems Architecture Science Research Division}
                                        %% \department is recommended
  \streetaddress{2-1-2 Hitotsubashi}
  \city{Chiyoda-ku}
  \state{Tokyo}
  \postcode{101-8430}
  \country{Japan}
}
\email{hsiang-shang@@nii.ac.jp}         %% \email is recommended

%% Author with two affiliations and emails.
\author{Zhenjiang Hu}
%\authornote{with author2 note}         %% \authornote is optional;
                                        %% can be repeated if necessary
%\orcid{nnnn-nnnn-nnnn-nnnn}            %% \orcid is optional
\affiliation{
  \position{Professor}
  \institution{National Institute of Informatics}
                                        %% \institution is required
%  \department{Information Systems Architecture Science Research Division}
                                        %% \department is recommended
  \streetaddress{2-1-2 Hitotsubashi}
  \city{Chiyoda-ku}
  \state{Tokyo}
  \postcode{101-8430}
  \country{Japan}
}
\additionalaffiliation{
  \position{Professor}
  \institution{SOKENDAI (The Graduate University for Advanced Studies)}
                                        %% \institution is required
%  \department{Department of Informatics}
                                        %% \department is recommended
  \streetaddress{Shonan Village}
  \city{Hayama}
  \state{Kanagawa}
  \postcode{240-0193}
  \country{Japan}
}
\email{hu@@nii.ac.jp}         %% \email is recommended


%% Paper note
%% The \thanks command may be used to create a "paper note" ---
%% similar to a title note or an author note, but not explicitly
%% associated with a particular element.  It will appear immediately
%% above the permission/copyright statement.
%\thanks{with paper note}               %% \thanks is optional
                                        %% can be repeated if necessary
                                        %% contents suppressed with 'anonymous'


%% Abstract
%% Note: \begin{abstract}...\end{abstract} environment must come
%% before \maketitle command
\begin{abstract}

Among the frameworks of bidirectional transformations proposed for addressing various synchronisation (consistency maintenance) problems, Foster~et~al.'s~[2007] asymmetric lenses have influenced the design of a generation of bidirectional programming languages.
Most of these languages are based on a declarative programming model, and only allow the programmer to describe a consistency specification with ad hoc and/or awkward control over the consistency restoration behaviour.
However, synchronisation problems are diverse and require vastly different consistency restoration strategies, and to cope with the diversity, the bidirectional programmer must have the ability to fully control and reason about the consistency restoration behaviour.
The putback-based approach to bidirectional programming aims to provide exactly this ability, and this paper strengthens the putback-based position by proposing the first fully fledged reasoning framework for a bidirectional language --- a Hoare-style logic for Ko~et~al.'s~[2016] putback-based language \BiGUL.
The Hoare-style logic lets the \BiGUL\ programmer precisely characterise the bidirectional behaviour of their programs by reasoning solely in the putback direction, thereby offering a unidirectional programming abstraction that is reasonably straightforward to work with and yet provides full control not achieved by previous approaches.
The theory has been formalised and checked in \Agda, but this paper presents the Hoare-style logic in a semi-formal way to make it easily understood and usable by the working \BiGUL\ programmer.

\end{abstract}


%% 2012 ACM Computing Classification System (CSS) concepts
%% Generate at 'http://dl.acm.org/ccs/ccs.cfm'.
\begin{CCSXML}
<ccs2012>
<concept>
<concept_id>10011007.10011006.10011050.10011017</concept_id>
<concept_desc>Software and its engineering~Domain specific languages</concept_desc>
<concept_significance>500</concept_significance>
</concept>
<concept>
<concept_id>10003752.10010124.10010131.10010135</concept_id>
<concept_desc>Theory of computation~Axiomatic semantics</concept_desc>
<concept_significance>500</concept_significance>
</concept>
<concept>
<concept_id>10003752.10003790.10011741</concept_id>
<concept_desc>Theory of computation~Hoare logic</concept_desc>
<concept_significance>500</concept_significance>
</concept>
</ccs2012>
\end{CCSXML}

\ccsdesc[500]{Software and its engineering~Domain specific languages}
\ccsdesc[500]{Theory of computation~Axiomatic semantics}
\ccsdesc[500]{Theory of computation~Hoare logic}
%% End of generated code


%% Keywords
%% comma separated list
\keywords{asymmetric lenses, putback-based bidirectional programming}  %% \keywords is optional


%% \maketitle
%% Note: \maketitle command must come after title commands, author
%% commands, abstract environment, Computing Classification System
%% environment and commands, and keywords command.
\maketitle


\section{Introduction}
\label{sec:introduction}

The need for synchronisation --- or \emph{consistency maintenance} --- is pervasive in computing.
A simple but typical example is synchronisation among documents of different formats, in which case consistency means that the
documents have the same content; whenever the content of one document is modified, the other documents should also be updated to restore the consistency.
%There are more complex scenarios as well: For example, in model-driven development, executable code is produced with respect to an abstract model describing high-level behaviour, and whenever the code is reorganised or the model is revised, the other side should be updated to maintain consistency --- in this case, consistency means that the behaviour of the code conforms to what the model specifies.
Over the past decade, frameworks of \emph{bidirectional transformations} have been proposed to address a diverse range of synchronisation problems~\citep{Czarnecki-BX}.
One such framework is \varcitet{Foster-lenses}{'s} \emph{asymmetric lenses}, which are highly influential such that the term \emph{bidirectional programming} has become largely synonymous with lens-based approaches (including lens combinators and bidirectionalisation; see, e.g., \citet{Foster-bidirectional-programming-approaches}).
Asymmetric lenses are designed for synchronising two pieces of data where one side, which is called the \emph{source}, has more information than the other, which is called the \emph{view}.
Typically, a lens program describes a forward |get| transformation that computes a consistent view from a source; whenever the source is modified, |get| is rerun to produce a new consistent view.
Conversely, from the same lens program we can derive a backward |put| transformation that takes a source and a (possibly modified) view, and produces an updated source that is consistent with the view and can retain some information of the original source.

By definition, the two transformations derived from any lens program should satisfy two inverse-like \emph{well-behavedness} laws called \ref{prop:PutGet} and \ref{prop:GetPut} (which will be formally stated in \autoref{thm:well-behavedness}).
\citet[Section~4.4]{Stevens-QVT} provided a revealing perspective to understand these well-behavedness laws: the |get| transformation denoted by a lens can be regarded as defining a (functional and executable) consistency relation on the source and view; \ref{prop:PutGet} then says that the |put| transformation will correctly restore the consistency, i.e., the updated source and the view will satisfy the consistency relation, and \ref{prop:GetPut} says that |put| will perform no update if the input source and view are already consistent.
From this perspective, at the root of \citeauthor{Foster-lenses}'s lenses and all subsequent \emph{|get|-based} approaches is a declarative programming model, in which the programmer specifies a consistency relation (in terms of a |get| transformation) and obtains a consistency restorer (a |put| transformation) that is guaranteed (by well-behavedness) to respect the consistency relation.
Mechanisms are provided for customising the restoration behaviour, but they are usually ad hoc and/or awkward to use.
This is unsatisfactory in practice, since we care not only about consistency but even more about how consistency restoration is performed; with |get|-based approaches it is inherently difficult to understand or control the latter aspect.
(See \autoref{sec:discussion} for further discussion.)

To be concrete, let us consider a simple synchronisation problem where the source is a pair of numbers representing the width and height of a rectangle, and the view is a single number, which is consistent with a rectangle exactly when it is equal to the width of the rectangle.
With respect to this definition of consistency, there are a variety of consistency restoration strategies: given a rectangle and a view, in addition to replacing the width with the view, which is necessary for restoring the consistency,
\begin{enumerate}[leftmargin=*,label=\arabic*.]
\item we can always keep the height unchanged --- this is a typical ``least-change'' strategy;
\item we can update the height to keep the height-to-width ratio of the rectangle --- in general this can be maintaining some kind of internal consistency on the source side;
\item we can reset the height to zero if the view is different from the width --- although rather drastic, this would be useful when the view side does not know how the source side maintains its internal consistency, and thus simply chooses to invalidate associated data and leave them for the source side to update later;
\item we can decide to keep or reset the height depending on whether the difference between the width and the view is small enough --- this is a flexible mixture of strategies 1~and~3;
\item we can use the height as a counter that is incremented every time an inconsistency is repaired --- though somewhat strange, in general this can be some form of logging of source changes.
\end{enumerate}
As we can see, even for a simple problem like rectangle width updating, there are already many possible update strategies; this is even more the case in complex, real-world scenarios.
All the above update strategies restore the same consistency but have different \emph{retentive} behaviour --- the way in which the information of the original source is retained --- to meet different requirements.
The programmer must be empowered to fully control and reason about the retentive behaviour of their programs to be sure that it is suitable for the intended applications.

Given that there are a myriad possibilities of update strategies, what can be better than having languages for \emph{programming} such strategies, capturing the myriad possibilities once and for all?
Following some previous work which took exactly this \emph{putback-based} programming approach~\citep{Pacheco-putlenses, Pacheco-BiFluX, Hu-putback-validity}, \citet{Ko-BiGUL} proposed a language \BiGUL\ (short for ``Bidirectional Generic Update Language'').
Like the original lenses, every \BiGUL\ program denotes a well-behaved pair of |put| and |get| transformations;
in contrast to the original lenses, \BiGUL\ is designed to express |put| transformations, and lets the programmer freely specify their intended update strategies.
Moreover, since |put| uniquely determines |get| by well-behavedness~(\autoref{lem:dominance}), the putback-based programmer is guaranteed that the |get| behaviour of their |put| program is unambiguously specified.
The putback-based approach thus offers a powerful alternative to bidirectional programming when full control is needed and the more declarative |get|-based approaches are not enough.
%However, due to the more intricate nature of \BiGUL's bidirectional semantics, it is still hard to guarantee that a \BiGUL\ program will exhibit the intended behaviour.

This paper strengthens the putback-based position by proposing the first fully fledged reasoning framework for a bidirectional language: building on a revised version of \BiGUL, we propose a \emph{Hoare-style logic}~\citep{Hoare-logic} that empowers the programmer to precisely characterise both the |put| and |get| behaviour of \BiGUL\ programs by reasoning \emph{exclusively in the putback direction}, thereby offering a unidirectional programming abstraction that is reasonably straightforward to work with and yet provides full control not achieved by |get|-based approaches.
For example, the programmer can express strategies 1~and~3 as two \BiGUL\ programs |keepHeight| and |resetHeight|, and with our Hoare-style logic, the programmer can prove two Hoare-style triples to make sure that the two programs correctly restore the consistency and have the intended retentive behaviour:
\begin{code}
(ASSERT(True)) ~  keepHeight   ~ (ASSERT((w', h') (_,  h) v | w' = v && h' = h))

(ASSERT(True)) ~  resetHeight  ~ (ASSERT((w', h') (w,  h) v | w' = v && (w = v => h' = h) && (w /= v => h' = 0)))
\end{code}
These two putback triples state that both |keepHeight| and |resetHeight| work on any input pairs of source and view (due to their always-true precondition) and will update the width with the view (|w' = v|), that |keepHeight| will retain the original height (|h' = h|), and that |resetHeight| will retain the height if the original width is equal to the view (|w = v => h' = h|) or reset the height otherwise (|w /= v => h' = 0|).
With a bit more reasoning about \emph{output range}, the programmer can also prove that the |get| transformations denoted by these two programs work on any input rectangle and extract its width, conforming to the consistency relation (|w' = v|) stated in the above triples.
(The other three rectangle width updating strategies can also be dealt with in the same way.)

Here are our contributions in a nutshell:
We define Hoare-style \emph{putback triples} for reasoning about the |put| behaviour of \BiGUL\ programs, prove that they are sound and complete, and show how they can also characterise the |get| behaviour to some extent~(\autoref{sec:putback-triples}).
The putback proof rules provide an axiomatic encapsulation of \BiGUL's semantics, and are designed for convenient domain-specific reasoning~(\autoref{sec:putback-proof-rules}).
Uniquely, to adequately characterise |get| behaviour, our Hoare-style logic also includes \emph{range triples} --- which are also sound and complete --- for estimating the output ranges of \BiGUL\ programs~(\autoref{sec:range-triples}).
We further propose rules for reasoning about recursive programs~(\autoref{sec:recursion}), and verify a \BiGUL\ implementation of key-based list alignment as a showcase example~(\autoref{sec:key-based-alignment}).
The presentation will be preceded by a recap of asymmetric lenses~(\autoref{sec:asymmetric-lenses}), and end with some discussion~(\autoref{sec:discussion}) and conclusion~(\autoref{sec:conclusion}).

%we will build a theory of putback triples in \autoref{sec:putback-triples}.
%\autoref{sec:putback-proof-rules} will then introduce the concrete putback proof rules along with \BiGUL's constructs, and give some derivation examples, including those for |keepHeight| (\autoref{ex:keepHeight}) and |resetHeight| (\autoref{ex:resetHeight}).
%\autoref{sec:range-triples} will complement putback triples with another set of \emph{range triples} so as to gain a better characterisation of the |get| behaviour of \BiGUL\ programs.
%\autoref{sec:recursion} will further develop proof rules for recursive \BiGUL\ programs, enabling us to verify a \BiGUL\ implementation of key-based list alignment in \autoref{sec:key-based-alignment} as a showcase example.
%After recapping some facts about asymmetric lenses in \autoref{sec:asymmetric-lenses}.
%Discussion and conclusion will follow in Sections \ref{sec:discussion}~and~\ref{sec:conclusion}.

Everything in this paper from theorems to derivation examples has been formalised and checked in \Agda\ version~2.5.2 with standard library version~0.13, but the \Agda\ formalisation is only provided as supplementary material.
This paper will focus on explaining the intuition, and present the Hoare-style logic in a semi-formal way to make it suitable for human reasoning.
\BiGUL\ is originally developed in \Agda\ and ported to \Haskell\ as an embedded language, and this influences the choices of the syntax and host language used in this paper:
our \BiGUL\ syntax is a hypothetical one abstracted from the \Haskell\ port of \BiGUL;
the host functional language is total and may be thought of as \Agda\ imperfectly disguised as \Haskell\ --- we will use some standard \Haskell\ types and functions, and allow some general recursion and partiality justifiable in a total setting.

%In an instance~\citep{Anjorin-BenchmarX-reloaded}, the \BiGUL\ program skipping all the dynamic checks runs about 20 times faster.

%\todo{display more things if possible}

\section{A Recap of Asymmetric Lenses}
\label{sec:asymmetric-lenses}

We start from a brief recap of some general facts about asymmetric lenses, but state these facts directly in terms of \BiGUL\ --- think of this section and the next as an introduction to the overall framework, rather than a detailed introduction to \BiGUL\ (which will be offered in \autoref{sec:putback-proof-rules}).
%These facts are true for \BiGUL\ programs in general and can be stated without referring to specific \BiGUL\ constructs, which we will introduce in \autoref{sec:putback-proof-rules}.%
%\todo{omit proof details related to semantics}
%\autoref{def:put-and-get} and \autoref{thm:well-behavedness} below are provided by \citet{Ko-BiGUL} for the original \BiGUL, whereas this paper uses a revised version of the language; accordingly, we have revised the internals of the definition and theorem, while keeping their statements the same.\todo{Refrain from presenting the denotational semantics to avoid introducing to much notation; axiomatic \emph{semantics} suffices to define the meaning of BiGUL. Actual introduction to come in \autoref{sec:putback-proof-rules}; these two sections are about asymmetric lenses in general}

Every \BiGUL\ program denotes an asymmetric lens, which is a \emph{well-behaved} pair of |put| and |get| transformations.
This is made precise by \autoref{def:put-and-get} and \autoref{thm:well-behavedness}.

\begin{definition} \label{def:put-and-get}
A \BiGUL\ program~|b| (whose possible forms are summarised in \autoref{fig:BiGUL}) operating on source type~|S| and view type~|V| is assigned the type |S <~ V|, and has two semantics:
\begin{code}
put  b : S -> V ->  Maybe S
get  b : S ->       Maybe V
\end{code}%
%\[ |put b : S -> V -> Maybe S| \AND |get b : S -> Maybe V| \]
The |put| --- or \emph{putback} --- semantics is also called the \emph{backward} semantics, and the |get| semantics is also called the \emph{forward} semantics.%
\footnote{In this paper we will provide an axiomatic semantics as the only formal definition of \BiGUL's semantics, and omit the definitions of |put| and |get| (except for a few simple cases in \autoref{sec:atomic}) and proofs that rely essentially on them (like the proof of \autoref{thm:well-behavedness}).
All the definitions and proofs are included in the supplementary \Agda\ formalisation for reference.}
\end{definition}

As noted by \citet{Ko-BiGUL}, the two transformations in \autoref{def:put-and-get} are potentially partial computations modelled explicitly as total |Maybe|-computations.
That is, |put b| and |get b| may fail to compute a result, in which case they produce |Nothing|; otherwise they return their result wrapped within the |Just| constructor.


\begin{theorem}[well-behavedness] \label{thm:well-behavedness}
Any \BiGUL\ program~|b| satisfies the following two \emph{well-behavedness} laws:
\begin{align}
& |all(s, v, s')| \quad |put b s v = Just s'| \quad|=>|\quad \awa{|put|}{|get|}\;|b|\;\awa{|s v|}{|s'|}\;|= Just v| \tag{\PutGet}\label{prop:PutGet} \\
& \awa{|all(s, v, s')|}{|all(s, v)|} \quad \awa{|put|}{|get|}\;\awa{|b s v|}{|b s|}\;|= Just|\;\awa{|s'|}{|v|} \quad|=>|\quad |put b s v = Just s| \tag{\GetPut} \label{prop:GetPut}
\end{align}
\end{theorem}

As noted by \citeauthor{Ko-BiGUL}, \autoref{thm:well-behavedness} gives a stronger well-behavedness guarantee~\citep{Macedo-composing-least-change-lenses, Pacheco-putlenses} than the original definition of \citet{Foster-lenses} --- in the original \PutGet, for example, a successful |put| computation does not guarantee the success of the subsequent |get| computation.
Even so, this theorem is not as practically useful as it seems because non-well-behavedness is merely swept under the partiality carpet: both |put b| and |get b| perform various checks at runtime to detect possible violations of well-behavedness, and if the programmer does not pay enough attention to well-behavedness requirements, the execution of |put b| or |get b| can unexpectedly fail one of these runtime checks (thereby satisfying \ref{prop:PutGet} or \ref{prop:GetPut} vacuously).
On the other hand, the theorem is still somewhat helpful since the BiGUL programmer no longer needs to worry about well-behavedness and can concentrate on totality, i.e., making sure that \BiGUL\ programs can compute successfully on the inputs that the programmer cares about.
%This is part of the motivation for developing the Hoare-style logic.

Well-behavedness implies that a putback transformation uniquely determines the corresponding forward transformation.
\begin{lemma}[\protect{\citet[Lemma~2.2.5]{Foster-thesis}}] \label{lem:dominance}
Let |l|,~|r : S <~ V|.
If |put l = put r| then |get l = get r|.
%\[ \IF |put l = put r| \THEN |get l = get r| \PERIOD \]
\end{lemma}
This lemma distinguishes asymmetric lenses from other models of bidirectional transformations (e.g., \varcitet{Hofmann-symmetric-lenses}{'s} symmetric lenses), and is the motivation behind \BiGUL's putback-based design, as it shows that it is theoretically feasible that the \BiGUL\ programmer can think and program solely in the putback direction and still unambiguously specify the forward behaviour.
This lemma does not help to explain what putback-based thinking is, though --- how does the programmer actually write a putback program while understanding its forward behaviour?
The key idea of this paper is that a Hoare-style logic can help to explain how that is achieved.
%In practice, however, this lemma is not too helpful in understanding forward behaviour, since the programmer may write a wrong putback program, in which case it does not help to know that there is a unique corresponding forward transformation, which is likely to be wrong as well.
%The idea of putback-based programming can truly succeed only if we can reason about putback programs sufficiently precisely, which we achieve in this paper with a Hoare-style logic.

\section{Theory of Putback Triples}
\label{sec:putback-triples}

Programming a putback transformation in \BiGUL\ is comparable to programming with states to some extent:
the \BiGUL\ programmer is given a source state and a view state, and manipulates the two states with the aim of transferring all information in the view to the source; in the end, the updated source state is returned as the result.
Reasoning about \BiGUL\ programs thus consists of tracking the properties satisfied by the states at each step, and it follows that a Hoare-style logic is well suited for performing this kind of reasoning about states.
We will introduce a set of Hoare-style triples for saying when \BiGUL\ programs (as putback transformations) can compute successfully and return results satisfying some specified properties.
Before doing so, we first need to fix our notation of relations (for specifying preconditions and postconditions).

\begin{notation}
Relations on types |(SUB A 1)|\kern1pt, |(SUB A 2)|\kern1pt, $\ldots,$ |(SUB A n)| are assigned the type |POWER((SUB A 1) TIMES (SUB A 2) TIMES {-"\cdots\;"-} TIMES (SUB A n))|.
When a relation~|R| of this type relates |(SUB a 1) : (SUB A 1)|\kern1pt, |(SUB a 2) : (SUB A 2)|\kern1pt, $\ldots,$ |(SUB a n) : (SUB A n)|\kern1pt, we write |R (SUB a 1) (SUB a 2) ... (SUB a n)|\kern1pt. %(in a curried form, to save parentheses and commas).
\end{notation}

\begin{definition}
\label{def:putback-triples}
A \emph{putback triple} is a \BiGUL\ program |b : S <~ V| surrounded by two \emph{putback assertions}:
\[ |(ASSERT R) ~ b ~ (ASSERT R')| \]
where |R : (POWER(S TIMES V))| is the \emph{precondition} (on the original source and the view) and |R' : (POWER(S TIMES S TIMES V))| is the \emph{postcondition} (on the updated source, the original source, and the view).%
\footnote{We do not require preconditions and postconditions to be syntactic entities drawn from a particular logic, but instead treat them semantically and will freely use whatever relations that are mathematically expressible.}
Valid putback triples are inductively defined by the proof rules in \autoref{fig:putback-proof-rules} (which will be explained in \autoref{sec:putback-proof-rules}).
\end{definition}

The intended meaning of a putback triple |(ASSERT R) b (ASSERT R')| is more or less standard: if the original source and the view satisfy the precondition~|R|, then |put b| will successfully produce an updated source satisfying the postcondition~|R'|, which can relate the updated source to the original source and the view.
We have proved that putback triples are sound and complete with respect to \BiGUL's |put| semantics.

\begin{theorem}[soundness and completeness of putback triples] \label{thm:putback-soundness-and-completeness}
Let |b : S <~ V|, |R : (POWER(S TIMES V))|, and |R' : (POWER(S TIMES S TIMES V))|.
\[ |(ASSERT R) ~ b ~ (ASSERT R')| \IFF |(all(s, v)) ~ R s v ~ => ~ (some(s')) ~ put b s v = Just s' ~ && ~ R' s' s v| \PERIOD \]
\end{theorem}

%The proof (as mentioned in \autoref{sec:asymmetric-lenses}) is omitted from the paper since it depends on the specific definition of |put|.
%Presentation-wise, we state the theorem to alleviate the doubt that there might not be any implementation fulfilling the axioms that we will see in \autoref{sec:putback-proof-rules}.

Given that putback behaviour completely determines forward behaviour~(\autoref{lem:dominance}), and that putback triples are about putback behaviour, shouldn't putback triples tell us something about forward behaviour as well?
This is indeed the case, as will be shown by \autoref{thm:partial-forward-consistency}.
Its statement will make use of some important definitions and notational conventions that will also be used throughout this paper.

\begin{definition}
A \emph{comprehension relation} of type |(POWER((SUB A 1) TIMES (SUB A 2) TIMES {-"\cdots\,"-} TIMES (SUB A n)))| has the form
\[ |COM(SUB pat 1 (SUB pat 2) ... (SUB pat n) || prop)| \]
where each |(SUB pat i)| is a pattern for elements of type~|(SUB A i)| and |prop| is a proposition that can refer to the variables in the patterns.
The patterns we use in the paper include variables, constructors, and the wildcard pattern~`|_|'.
The relation holds for |(SUB a 1) : (SUB A 1)|, |(SUB a 2) : (SUB A 2)|, $\ldots,$ |(SUB a n) : (SUB A n)| exactly when each |(SUB a i)| matches |(SUB pat i)| and |prop| holds after substituting the matched components for the corresponding pattern variables.
\end{definition}

\begin{notation} \label{notation:trivially-true-proposition}
We usually omit the proposition part of a comprehension relation when the proposition is trivially true, keeping only the pattern part.
For example, |COM((_ :: _))| holds exactly for non-empty lists, and |COM(_ _)| is the always-true binary relation.
\end{notation}

\begin{notation} \label{notation:angle-brackets}
The angle brackets delimiting a comprehension relation may be omitted where delimitation is unnecessary, like in an assertion containing only a comprehension relation.
For example, |ASSERT(COM(s v || s = v))| is abbreviated to |ASSERT(s v || s = v)|.
\end{notation}

\begin{definition}
The \emph{graph} of a function |f : A -> Maybe B| is a relation |GRAPH f : (POWER(A TIMES B))| which relates |a : A| and |b : B| exactly when |f a = Just b|.
\end{definition}

\begin{theorem}[partial forward consistency] \label{thm:partial-forward-consistency}
Let |b : S <~ V|, |R : (POWER(S TIMES V))|, and |C : (POWER(S TIMES V))|.
\[ \IF |(ASSERT R) ~ b ~ (ASSERT(s' _ v || C s' v))| \THEN |GRAPH(get b) CAP R ~ SUBSETEQ ~ C| \PERIOD \]
\end{theorem}
\begin{proof}
Suppose |get b s = Just v| and |R s v|.
The latter assumption triggers \autoref{thm:putback-soundness-and-completeness}, so we know that |put b s v = Just s'| for some~|s'| and that |C s' v| holds.
On the other hand, by \ref{prop:GetPut}, we can turn the first assumption |get b s = Just v| into |put b s v = Just s|.
Seeing that |put b s v| computes to both |s'|~and~|s|, we can deduce |s' = s|, and thus having |C s' v| is the same as having |C s v|.
\end{proof}

That is, if we can prove that a putback transformation establishes consistency~|C| between the updated source and the view, then, roughly speaking, a part of the behaviour of the corresponding forward transformation will be constrained by~|C|.
We call \autoref{thm:partial-forward-consistency} \emph{partial} forward consistency for two reasons.
The first reason is that \autoref{thm:partial-forward-consistency} does not guarantee that the entire graph of the forward transformation will be contained in~|C| --- the containment is guaranteed only for the part of the graph that falls within~|R|.
In practice, this makes \autoref{thm:partial-forward-consistency} not very helpful unless |R|~is always true, in which case the entire graph will indeed be contained in~|C|.
Even in this case, though, there is still the second reason: \autoref{thm:partial-forward-consistency} says nothing about the totality of the forward transformation, i.e., on which subset of sources the forward transformation can successfully produce results.
We will augment \autoref{thm:partial-forward-consistency} to get a practically useful version (\autoref{thm:total-forward-consistency}).
But before that, let us look at the concrete putback proof rules and some examples of putback reasoning.

\section{\BiGUL\ and the Putback Proof Rules}
\label{sec:putback-proof-rules}

\begin{figure}

$\begin{array}{c}
\\ \hline
|fail : S <~ V|
\end{array}$
\rulehsep
$\begin{array}{c}
\\ \hline
|replace : S <~ S|
\end{array}$
\rulehsep
$\begin{array}{c}
|f : S -> V| \\ \hline
|skip f : S <~ V|
\end{array}$
\rulehsep
$\begin{array}{c}
|l : S <~ V| \rulepsep
|r : T <~ W| \\ \hline
|l * r : (S TIMES T) <~ (V TIMES W)|
\end{array}$

\rulevsep

$\begin{array}{c}
|vpat : Pat V| \rulepsep |wpat : Pat W| \rulepsep |b : S <~ W| \\ \hline
|rearrV vpat -> wpat INNER b : S <~ V|
\end{array}$
\rulehsep
$\begin{array}{c}
|spat : Pat S| \rulepsep |tpat : Pat T| \rulepsep |b : T <~ V| \\ \hline
|rearrS spat -> tpat INNER b : S <~ V|
\end{array}$

\rulevsep

$\begin{array}{c}
|bs : (SEQ(Branch S V))| \\ \hline
|case INNER bs : S <~ V|
\end{array}$
\rulehsep
$\begin{array}{c}
|M : (POWER(S TIMES V))| \rulepsep |E : (POWER S)| \rulepsep |b : S <~ V| \\ \hline
|normal M exit E INNER b : Branch S V|
\end{array}$
\rulehsep
$\begin{array}{c}
|M : (POWER(S TIMES V))| \rulepsep |f : S -> V -> S| \\ \hline
|adaptive M INNER f : Branch S V|
\end{array}$

\caption{\BiGUL\ constructs and their typing (simplified).
|Pat| and |SEQ(-)| are hypothetical type constructors for patterns and sequences respectively. The symbol~`\protect\scalebox{.75}{\protect\rotatebox[origin=c]{180}{\ensuremath{\Lsh}}}' indicates that its right-hand side is syntactically a sub-node of its left-hand side; in displayed code, the right-hand side is typeset in an indented block.}
\label{fig:BiGUL}

\end{figure}

\begin{figure}

$\begin{array}[t]{c} \hline
|(ASSERT EMPTY) ~ fail ~ (ASSERT EMPTY)|
\end{array}$
\rulehsep
$\begin{array}[t]{c} \hline
|(ASSERT(_ _)) ~ replace ~ (ASSERT(s' _ v || s' = v))|
\end{array}$
\rulehsep
$\begin{array}[t]{c} \hline
|(ASSERT(s v || f s = v)) ~ skip f ~ (ASSERT(s' s _ || s' = s))|
\end{array}$

\rulevsep

$\begin{array}[t]{c}
|(ASSERT L) ~ l ~ (ASSERT L')| \rulepsep
|(ASSERT R) ~ r ~ (ASSERT R')| \\ \hline
|(ASSERT(L * R)) ~ l * r ~ (ASSERT(L' * R'))|
\end{array}$
\rulehsep
$\begin{array}[t]{l}
|T ~ SUBSETEQ ~ R| \rulepsep
|{-"\assert{\awa{T}{R}}\;"-} ~ b ~ {-"\;\assert{\awa{T^\prime}{R^\prime}}"-}| \rulepsep
|R' CAP (COM(_ s v || T s v)) ~ SUBSETEQ ~ T'| \\ \hline
\phantom{|T ~ SUBSETEQ ~ R| \rulepsep}|{-"\assert{T}\;"-} ~ b ~ {-"\;\assert{T^\prime}"-}|
\end{array}$

\rulevsep

$\begin{array}[t]{c}
|(ASSERT(s wpat || R s (ENV(wpat)))) ~ b ~ (ASSERT(s' s wpat || R' s' s (ENV(wpat))))| \\ \hline
\adjustrearr |(ASSERT(s vpat || R s (ENV(vpat)))) ~ rearrV vpat -> wpat INNER b ~ (ASSERT(s' s vpat || R' s' s (ENV(vpat))))|
\end{array}$

\rulevsep

$\begin{array}[t]{c}
|(ASSERT(tpat v || R (ENV(tpat)) v)) ~ b ~ (ASSERT(tpat' tpat v || R' (ENV(tpat')) (ENV(tpat)) v))| \\ \hline
\adjustrearrmore |(ASSERT(spat v || R (ENV(spat)) v)) ~ rearrS spat -> tpat INNER b ~ (ASSERT(spat' spat v || R' (ENV(spat')) (ENV(spat)) v))|
\end{array}$

\rulevsep

$\begin{array}[t]{ll}
|all((normal M exit E INNER b) `elem` bs)| \\
\hspace{.5em} |(ASSERT(R CAP (NORM M))) ~ b ~ (ASSERT(R' CAP (COM(s' _ v || (NORM M) s' v && (NORM E) s'))))| \\
|all((adaptive M INNER f) `elem` bs)| \\
\hspace{.5em} |all(s, v) ~ (R CAP (NORM M)) s v ~ =>| \\
\hspace{.5em}\phantom{|all(s, v) ~ ~|}\quad\,\phantom{|&&|}\ \ |(R CAP NormalDomain) (f s v) v|
& |where| \\
\hspace{.5em}\phantom{|all(s, v) ~ ~|}\quad\,|&&|\ \ |(all(s')) R' s' (f s v) v => R' s' s v|
& \hspace{.4em} |NormalDomain = BIGCUP ~ [ (NORM M) || (normal M ...) `elem` bs ]| \\ \cline{1-1}
\multicolumn{1}{c}{|(ASSERT(R CAP Domain)) ~ case INNER bs ~ (ASSERT R')|}
& \hspace{.4em} |{-"\awa{\mathcal N}{\mathcal D}\;"-} = BIGCUP ~ [ M || (normal OR adaptive M ...) `elem` bs ]|
\end{array}$

\caption{Putback proof rules. |NORM M| denotes the ``actual main condition'' of a branch: the main condition~|M| of the branch intersected with the negations of the main conditions of all the previous branches. ``Actual exit conditions'' |NORM E| are analogous.}
\label{fig:putback-proof-rules}

\end{figure}

In this section we introduce \BiGUL's constructs~(\autoref{fig:BiGUL}) and their putback proof rules~(\autoref{fig:putback-proof-rules}).
%Except for the consequence rule (the right one in the second row), every rule corresponds to a \BiGUL\ construct and gives an axiomatic encapsulation of its semantics.
For each construct, we will give its type --- which is essential for inferring the types of entities in assertions --- and explain the corresponding proof rule with the help of an operational intuition about the construct.
%\footnote{As \autoref{thm:putback-soundness-and-completeness} shows that the proof rules precisely capture \BiGUL's |put| semantics, we take \autoref{fig:putback-proof-rules} to be the definition of \BiGUL's (axiomatic) semantics in this paper, and will not give the definition of |put| formally.}
%We will not, however, go into the rationale behind the design of the constructs, for which the interested reader is referred to \citet[Section~5]{Hu-BiGUL-tutorial}.

Note that assertions are intended to be semantic rather than syntactic --- for example, if the precondition stated in a rule is |COM(_ _)|, we will regard the rule as directly applicable when the actual precondition is, say, |COM(s v || s = s && v = v)|, which differs from |COM(_ _)| syntactically but still denotes the always-true binary relation semantically.
%Also, all assertions in triples are strongly typed according to \autoref{def:putback-triples}; for example, the source and view types of |replace| are required to be the same; consequently, |s'|~and~|v| in the corresponding proof rule's postcondition are of the same type, and it is sensible to talk about equality between them.

\subsection{Atomic Constructs}
\label{sec:atomic}

\BiGUL\ has three atomic constructs, whose corresponding rules are in the first row of \autoref{fig:putback-proof-rules}.

The |fail| construct has type |S <~ V| for any types |S|~and~|V|.
The precondition of the |fail| rule is the empty relation~|EMPTY|, saying that no input can make |fail| compute successfully.
This directly corresponds to the implementation: |put fail s v = Nothing|.
%(On the other hand, the postcondition can be any relation because of the consequence rule, which we will discuss in \autoref{sec:putback-consequence-rule}.)

The |replace| construct has type |S <~ S| for any type~|S|, and replaces the source with the view regardless of what they are, i.e., |put replace s v = Just v|.
Correspondingly, the precondition of the |replace| rule is the always-true relation, and the postcondition states that the updated source~|s'| will be equal to the view~|v|.

The |skip| construct takes a function |f : S -> V| in the host language as an argument and has type |S <~ V|.
It ignores the view and leaves the source as it is; correspondingly, the postcondition says that the updated source~|s'| will be equal to the original source~|s|.
Unlike |replace|, we cannot |skip| under all circumstances --- before throwing the view away, we must ensure that it can be recovered from the source, or otherwise there is no hope to establish \ref{prop:PutGet}.
The precondition thus requires that the view can be computed from the source by~|f|.
In the implementation, this precondition is checked dynamically: |put (skip f) s v = if f s == v then Just s else Nothing|.

\subsection{Product}
\label{sec:product}

Given two \BiGUL\ programs |l : S <~ V| and |r : T <~ W|, we can form the product of the two programs |l * r : (S TIMES T) <~ (V TIMES W)|, with |l|~operating on the first components and |r|~on the second components.
If two putback triples with preconditions |L|~and~|R| have been established for |l|~and~|r|, the precondition of the product program will be
\[ |L * R ~ = ~ (COM((s, t) (v, w) || L s v && R t w))| \]
The relation-level `|*|'~operator can be seen as a simple variant of separating conjunction~\citep{Reynolds-separation-logic}, and can be defined arity-generically to construct a relation on $n$~pairs from an $n$-ary relation on all the first components and the other on all the second components.
The postcondition can then be stated also in terms of this `|*|'~operator.

\begin{example}[parallel replacement] \label{ex:replace-squared}
We can now construct simple derivations like the following one for |replace * replace|, which we use as an example to explain our derivation format:
\begin{code}
(ASSERT(_ _))
^  (ASSERT(_ _))
^  replace
^  (ASSERT(s' _ v | s' = v))
*  (ASSERT(_ _))
^  replace
^  (ASSERT(t' _ w | t' = w))
(ASSERT((s', t') _ (v, w) | s' = v && t' = w))
\end{code}
First note that the syntax tree structure of |replace * replace| is reflected in indentation: the top-level node is~`|*|', whose two sub-nodes --- both being |replace| --- are indented to the next level.
Then, following the indentation structure, the assertions are added: the assertions about a node are put on the same indentation level as the node, with the precondition and postcondition appearing respectively before and after the node.
This format is compact and yet retains the tree structure of the derivation, making it easier to check the correctness of the derivation.
%(Auxiliary dotted lines are also added to make indentation levels clearer, especially when derivations spread across pages.)
\end{example}

\subsection{The Consequence Rule}
\label{sec:putback-consequence-rule}

The consequence rule we present in \autoref{fig:putback-proof-rules} (the right one in the second row) may seem unusual, but first observe that it is a stronger version of the usual one (so at least there is nothing to lose):
\begin{equation}
\begin{array}{l}
|T ~ SUBSETEQ ~ R| \rulepsep
|{-"\assert{\awa{T}{R}}\;"-} ~ b ~ {-"\;\assert{\awa{T^\prime}{R^\prime}}"-}| \rulepsep
|R' ~ SUBSETEQ ~ T'| \\ \hline
\phantom{|T ~ SUBSETEQ ~ R| \rulepsep}|{-"\assert{T}\;"-} ~ b ~ {-"\;\assert{T^\prime}"-}|
\end{array}
\label{eq:usual-consequence-rule}
\end{equation}
To see why we need a stronger consequence rule, consider deriving this triple:
\[ |(ASSERT(_ (v, w) || v = w)) ~ replace * replace ~ (ASSERT((s', t') _ _ || s' = t'))| \]
where there is some entanglement between the first and second components in the precondition and postcondition, so the product rule is not directly applicable.
We could try to extend the derivation in \autoref{ex:replace-squared} using the usual consequence rule~(\ref{eq:usual-consequence-rule}):
\begin{code}
(ASSERT(_ (v, w) | v = w))
(ASSERT(_ _))
replace * replace
(ASSERT((s', t') _ (v, w) | s' = v && t' = w))
VDOTS
(ASSERT((s', t') _ _ | s' = t'))
\end{code}
Adjacent assertions on the same indentation level indicate an invocation of the consequence rule, with the one above implying the one below.
In the first two lines of this derivation, there is one such invocation, which turns |(COM(_ (v, w) || v = w))| into |(COM(_ _))| so that the product rule can apply.
On the other hand, the postcondition that we can establish, i.e., |(COM((s', t') _ (v, w) || s' = v && t' = w))|, does not imply the postcondition we want to establish, i.e., |(COM((s', t') _ _ || s' = t'))|.
%(hence the vertical dots separating the two postconditions in the derivation, to avoid suggesting that the consequence rule is invoked)
The usual consequence rule~(\ref{eq:usual-consequence-rule}) can help us to get rid of the entanglement |v = w|, but that entanglement is needed to establish the final implication (by |s' = v = w = t'|).
We thus need the stronger consequence rule to be able to carry over whatever we know about the original source and the view from the precondition to the postcondition.
When working in our derivation format, the stronger consequence rule allows us to prove an implication between adjacent postconditions using whichever preconditions for the same node (on the same indentation level) as additional premises about the original source and the view.%
\footnote{Alternatively and equivalently, as suggested by an anonymous reviewer of an earlier version of this paper, we can keep the usual consequence rule~(\ref{eq:usual-consequence-rule}) and introduce a separation logic--style frame rule: |(ASSERT R) b (ASSERT R')| $\Rightarrow$ |(ASSERT(R CAP T)) b (ASSERT(R' CAP (COM(_ s v || T s v))))|, which is somewhat more elegant.
However, we feel that being able to use preconditions to establish implications between postconditions is more convenient in practice, and the stronger consequence rule captures this ability more directly.}

%The stronger consequence rule also simplifies other rules.
%For example, if we only had the usual consequence rule~(\ref{eq:usual-consequence-rule}), we would have to enrich the |skip| rule to something like:
%\[ \begin{array}[t]{c} \hline
%|(ASSERT(s v || f s = v && R s v)) ~ skip f ~ (ASSERT(s' s _ || s' = s && R s' v))|
%\end{array} \]
%saying additionally that whatever is true for the original source and the view in the precondition is also true for the updated source and the view in the postcondition.
%This enriched |skip| rule can be derived from the simpler one given in \autoref{fig:putback-proof-rules} and the stronger consequence rule.

\subsection{Rearrangement}

A guiding intuition for \BiGUL\ programming is to manipulate the source and view to make their shapes match, which is achieved mainly with the \emph{rearrangement} operations.
To provide a more concrete motivation:
We have seen that the product combinator (\autoref{sec:product}) allows us to synchronise source and view tuples of arbitrary size, provided that their structures are the same.
When this is not the case, in \BiGUL\ we can use a simple class of pattern-matching $\lambda$-expressions to rearrange the source and/or the view to make them match structurally and ready for further synchronisation.
For example, the height-keeping strategy~1 we proposed for the rectangle width updating problem (\autoref{sec:introduction}) can be expressed in \BiGUL\ as:
\begin{code}
keepHeight  : (Nat TIMES Nat) <~ Nat
keepHeight  =  rearrV v -> (v, ())
               ^  ^  replace        -- |const| is the K~combinator (|const x y = x|), and
               ^  *  skip const ()  -- `|()|' is the sole inhabitant of the unit type
                                    
\end{code}
Initially, the view is a single number, whereas the source is a pair.
To make their structures match, we use the view rearrangement operation |rearrV v -> (v, ())| to apply the $\lambda$-expression |\ v -> (v, ())| to the view and make the result the new view.
Inside the |rearrV|, the source and view are both pairs, so we can use |replace * skip const ()| to update the width and keep the height as it is.
Below we will mainly discuss view rearrangement; source rearrangement is largely analogous, and will be discussed towards the end of this subsection.

\varparagraph{View rearrangement.}
The general form of a view rearrangement is |rearrV vpat -> wpat INNER b :| |S <~ V|, where |vpat| is a pattern for the original view type~|V|, |wpat| is a ``pattern'' for a new view type~|W|, and the inner program~|b| has type |S <~ W|.
(The symbol~`|INNER|' indicates that |b|~is syntactically a sub-node of `|rearrV vpat -> wpat|'; in displayed code, |b|~is typeset in an indented block below `|rearrV vpat -> wpat|'.)
The intention is to represent a closed $\lambda$-expression |\ vpat -> wpat| to be applied to the view.
Strictly speaking, |wpat| is not a pattern but an expression, which can be built using variables in |vpat| and constructors.
(Apart from the fact that |wpat| looks similar to a pattern, we will explain why it is beneficial to think of |wpat| as a pattern shortly.)
Wildcards are not allowed in |vpat|, and all variables in |vpat| must appear in |wpat| and can appear multiple times --- these synctactic restrictions ensure that the $\lambda$-expression is invertible, or, more intuitively speaking, does not lose information.

\varparagraph{The view rearrangement rule.}
Intuitively, a rearrangement only massages the state into an alternate shape suitable for further processing, rather than applying an arbitrary and distorting transformation.
This intuition significantly influences the design of the rearrangement rules, which reflect that rearrangement is essentially just a ``change of perspective''.
If we are rearranging the view from |vpat| to |wpat|, it must mean that the view matches |vpat| right before the rearrangement, and we should be able to state properties satisfied by the view at that point in terms of its components.
The precondition for |rearrV| is thus a comprehension relation:
\[ |(COM(s vpat || R s (ENV(vpat))))| \]
which requires that the view matches |vpat| and that any properties about the view are stated in terms of the variables in |vpat|, which we denote by |(ENV(vpat))|.
%(A more common notation is $\mathrm{FV}(|vpat|)$, which disrupts the presentation of the rearrangement rules however.)
After the rearrangement, due to the invertibility restrictions, the new view will retain all the components of the original view; the components may be shuffled around and duplicated, but whatever we knew about the components will remain true.
The precondition for the inner program~|b| is thus:
\[ |(COM(s wpat || R s (ENV(wpat))))| \]
This inner precondition asserts that the new view matches |wpat| and that whatever holds for |(ENV(vpat))| in the outer precondition also holds here for |(ENV(wpat))|, which is the same as |ENV(vpat)| because of the invertibility restrictions.
Being able to state this inner precondition is the reason that we think of |wpat| also as a pattern, even though that means in general we have to allow non-linear patterns, where multiple occurrences of the same variable indicate implicitly that values at those positions should be equal.
When using the rule in actual derivations, the two preconditions will differ only in their view patterns and have the same proposition part.
Therefore, the view rearrangement rule only changes the shape we expect the view to take, not the properties we know about the content of the view.
This change-of-perspective interpretation works for the postconditions as well.

\begin{example}[rectangle width updating --- keeping the height]
\label{ex:keepHeight}
We can now verify |keepHeight| as follows, where the precondition (assertion~1) is always true and the postcondition (assertion~2) says that the consistency will be established (|w' = v|) and the height will be retained (|h' = h|):
\begin{code}
(ASSERT(_ _))(ASSERTNUMBER *1)
rearrV v -> (v, ())
^   (ASSERT(_ (_, ())))(ASSERTNUMBER *3)
^  ^  (ASSERT(_ _))
^  ^  replace
^  ^  (ASSERT(w' _ v | w' = v))
^  *  (ASSERT(_ ()))
^  ^  (ASSERT(h v | const () h = v))
^  ^  skip const ()
^  ^  (ASSERT(h' h _ | h' = h))
^  ^  (ASSERT(h' h () | h' = h))
^  (ASSERT((w', h') (_, h) (v, ()) | w' = v && h' = h))(ASSERTNUMBER *4)
(ASSERT((w', h') (_, h) v | w' = v && h' = h))(ASSERTNUMBER *2)
\end{code}
Note that when constructing the derivation inwards from the initial precondition and postcondition, it is effortless to push them inside the |rearrV| and turn them into assertions 3~and~4 just by changing the view pattern to a pair pattern, as instructed by the |rearrV|.
\end{example}

\varparagraph{Source rearrangement and the corresponding rule.}
Analogous to view rearrangement, the general form of a source rearrangement is |rearrS spat -> tpat INNER b : S <~ V|, where |spat| is a pattern for the original source type~|S|, |tpat| is a pattern for the new source type~|T|, and the inner program~|b| has type |T <~ V|.
The same syntactic restrictions for invertibility apply to |spat| and |tpat|.
Operationally, the source is transformed using |\ spat -> tpat|, and |b| is executed on the new source and the view; after that, the updated source must match |tpat|, and will be transformed back to the shape of |spat| (as if evaluating |\ spat -> tpat| backwards).
Dual to the view rearrangement rule, the source rearrangement rule also reflects a change of perspective by varying the source patterns.
Notably, the postcondition for~|b|
\[ |COM(tpat' tpat v || R' (ENV(tpat')) (ENV(tpat)) v)| \]
says explicitly that the updated source produced by~|b| should match |tpat'| (which is just |tpat| with its variables freshly renamed, to avoid name clashes with those variables in the other occurrence of |tpat|), which is a requirement often overlooked by novice \BiGUL\ programmers.

\begin{example}[view equality checking] The following small program implements the equality checking operator in reversible programming (see, e.g., \citet{Thomsen-rFun}):
\begin{code}
eqCheck : Eq A => ~ A <~ (A TIMES A)
eqCheck =  rearrS x -> (x, x)
           ^ replace
\end{code}
where the `|Eq A|' constraint in the type indicates that we need decidable equality on~|A| for the program to be executable.
This example shows that |rearrS| can impose restrictions on the result produced by the inner program: Operationally, the source is rearranged with the $\lambda$-expression |\ x -> (x, x)|, and then the inner program |replace| is executed, after which the rearranging $\lambda$-expression is evaluated backwards by matching the replaced source with the non-linear pattern |(x, x)| --- in effect checking whether the components are equal --- and then returning one of the components.
For this computation to succeed, the replaced source --- i.e., the input view --- must be a pair of duplicate values.
In the derivation for |eqCheck| below, this restriction appears in assertion~1 (as the non-linear pattern |(s', s')| for the updated source), arising from the use of the |rearrS| rule.
\begin{code}
(ASSERT(_ (v, w) | v = w))
rearrS x -> (x, x)
^ (ASSERT((s, s) (v, w) | v = w))
^ (ASSERT(_ _))
^ replace
^ (ASSERT((s', t') _ (v, w) | s' = v && t' = w))
^ (ASSERT((s', s') (s, s) (v, w) | s' = v && s' = w))(ASSERTNUMBER *1)
(ASSERT(s' _ (v, w) | s' = v && s' = w))
\end{code}
\end{example}


%\varparagraph{Formalisation.}
%The rearrangement rules we have presented rely essentially on pattern-matching comprehension relations, but the actual \Agda\ formalisation takes a different approach and avoids modelling pattern-matching comprehension relations entirely.
%The formalisation is sketched here for the curious (and perhaps sceptical) reader.
%We build on \varcitet{Ko-BiGUL}{'s} formalisation of pattern matching, which makes use of heavily indexed types to guarantee various kinds of safety.
%To avoid introducing the heavy \Agda\ notation, below we will give a simplified account, hiding all parameters and indices.
%Suppose that we are rearranging the view from |vpat| for type~|V| to |wpat| for type~|W|.
%The actual formalisation first defines a type |PatResult|: an inhabitant of |PatResult| is the result of matching a value of type~|V| with |vpat|, and can be thought of as a mapping from every variable in |vpat| to the component matching the variable.
%Two relations are then defined: |Match : (POWER(V TIMES PatResult))| relates |v : V| and |r : PatResult| exactly when |v|~matches |vpat| and |r|~is the result of the matching, and |Eval : (POWER(PatResult TIMES W))| relates |r : PatResult| and |w : W| exactly when |w|~is the result of evaluating |wpat| (as an expression) using |r|~as the environment.
%With these two relations, we state the precondition for the whole |rearrV| program as |(COM(s v || (some(r)) Match v r && R s r))|, and the precondition for the inner program as |(COM(s w || (some(r)) Eval r w && R s r))|, making no use of pattern-matching comprehension relations.


\subsection{Case Analysis}

More sophisticated programs require case analysis, for which \BiGUL\ provides a powerful and intricate |case| construct.
For a simple example, the height-resetting strategy~3 for the rectangle width updating problem (\autoref{sec:introduction}) can be expressed as:
\begin{code}
resetHeight : (Nat TIMES Nat) <~ Nat
resetHeight =  case
               ^  normal (w, _) v | w = v exit _
               ^  ^  skip fst
               ^  adaptive _ _
               ^  ^  \ _ v -> (v, 0)
\end{code}
Roughly speaking, this program checks whether the width of the source is equal to the view, and skips if that is the case; otherwise, it creates a new rectangle whose width is the view and whose height is zero.

\varparagraph{Syntax of\, |case|.}
In general, a case analysis in \BiGUL\ has the form |case INNER bs : S <~ V| where |bs|~is a sequence of |normal| or |adaptive| branches.
For normal branches, the general form is |normal M exit E INNER b| where |M : (POWER(S TIMES V))| is called the \emph{main condition}, |E : (POWER S)| is called the \emph{exit condition}, and |b : S <~ V| is the branch body.
For adaptive branches, the general form is |adaptive M INNER f| where |M : (POWER(S TIMES V))| is again the main condition, and |f : S -> V -> S| is a function in the host language.
The syntactic conventions described by \autoref{notation:trivially-true-proposition} and \autoref{notation:angle-brackets} are also adopted for comprehension relations used as main or exit conditions.%
\footnote{We make |M|~and~|E| comprehension relations to simplify the presentation --- in real, executable programs, |M|~and~|E| should be ``comprehension expressions'' that compute to boolean values instead of propositions, but that would mess up the assertions where we would have to write propositions like |M s v = true| instead of just |M s v|.}
%We are careful not to sacrifice computability, though: the comprehension relations we use as conditions in this paper can all be straightforwardly converted to ``comprehension expressions'' in real programs.

\varparagraph{The\/ |case| rule.}
Operationally, the execution of a |case| finds the first branch whose main condition is satisfied by the source and view, and enters that branch.
Suppose that the precondition and postcondition we want to verify for the entire |case| are |R|~and~|R'| respectively.
The |case| rule in \autoref{fig:putback-proof-rules} says that the precondition should be restricted to |R CAP Domain| where |Domain| is the union of all the main conditions, so that the precondition is strong enough to guarantee that some branch will be entered.
%(Of course, the consequence rule allows us to use just~|R| as the precondition if |R SUBSETEQ Domain|.)
The rest of the job is to verify each branch.

\varparagraph{Normal branches.}
If a normal branch |normal M exit E INNER b| is entered, its body~|b| is executed; the |case| rule thus requires us to verify the behaviour  of~|b| by deriving the following triple:
\[ |(ASSERT(R CAP (NORM M))) ~ b ~ (ASSERT(R' CAP (COM(s' _ v || (NORM M) s' v && (NORM E) s'))))| \]
The precondition is strengthened with the main condition since we know that the source and view must satisfy the main condition if the branch is entered.
However, the precise condition satisfied is not~|M| --- since the branches are tried in order and a branch is entered only when the main conditions of all the previous branches are not satisfied, we should regard the actual main condition of a branch as |M|~intersected with the negations of the main conditions of all the previous branches.
We denote this actual main condition by~|NORM M|, and the precondition for~|b| is strengthened to |R CAP (NORM M)|.
%(The programmer can avoid distinguishing actual and ``superficial'' main conditions by writing programs where the main conditions are all disjoint, in which case |NORM M = M|.)
As for the postcondition, in addition to~|R'|, we also require \,(i)~that the updated source and the view satisfy the actual main condition~|NORM M| and \,(ii)~that the updated source satisfy the actual exit condition |NORM E|, which is |E|~intersected with the negations of the exit conditions of all the previous normal branches.
These requirements are essential for guaranteeing well-behavedness; for a detailed development of these requirements, see \citet[Section~5.5]{Hu-BiGUL-tutorial}.
%Requirement~(i) is for avoiding branch switching, while requirement~(ii) makes exit conditions analogous to ``assertions'' in reversible conditionals~\citep{Yokoyama-Janus}.

\varparagraph{Adaptive branches.}
Requirement~(i) above for normal branches turns out to be very restrictive, making normal branches only capable of dealing with ``almost consistent'' cases in practice.
However, we often need branches whose main condition describes a particular kind of inconsistency and whose purpose is to repair that inconsistency --- that is, their main conditions are supposed to be broken after updating, and this is against the nature of normal branches.
Instead, for repairing inconsistency, we use adaptive branches, which are comparable with \varcitet{Foster-lenses}{'s} ``fixup functions''.
When entered, an adaptive branch |adaptive M INNER f| applies~|f| to the source and view to produce an adapted source; this adapted source then takes the place of the original source, and the whole |case| is rerun.
Naturally, requirements have to be imposed on~|f|, as stated in the |case| rule:
\begin{align*}
|all(s, v)| \quad |(R CAP (NORM M)) s v| &\quad|=>|\quad |(R CAP NormalDomain) (f s v) v| \\
& \quad\awa{|=>|}{\kern1.5pt|&&|}\quad |(all(s')) ~ R' s' (f s v) v ~ => ~ R' s' s v|
\end{align*}
Like normal branches, we know that |R|~and~|NORM M| hold for the original source~|s| and the view~|v|, and that has to be strong enough to make |s|~and~|v| satisfy two requirements:
\begin{itemize}[leftmargin=*]
\item First, the adapted source |f s v| and the view~|v| can make the whole |case| rerun successfully.
That is, they should satisfy~|R|, the precondition for the entire |case|, and also |NormalDomain|, which denotes the union of the actual main conditions of the |normal| branches --- this ensures that the rerunning will go into a normal branch and terminate there, instead of revisiting adaptive branches indefinitely.
\item Second, the rerunning of the |case| establishes the postcondition for the updated source, the adapted source, and the view, but ultimately we want the postcondition established not for the adapted source but the original source.
Therefore, whichever updated source~|s'| is produced by the rerunning, the postcondition |R' s' (f s v) v| established by the rerunning has to be sufficient for the ultimate postcondition |R' s' s v|.
\end{itemize}
In practice, the first requirement leads us to write adaptive behaviour that performs enough inconsistency-repairing so as to be able to go back into normal branches, while the second requirement discourages us from radically changing the source during adaptation so that it is possible to derive properties about the original source from properties about the adapted source.
(We will see how these two guidelines are applied in a more illustrative scenario in \autoref{sec:key-based-alignment}.)

\varparagraph{Representing the\/ |case| rule in our derivation format.}
Before we see some derivation examples, we need to think about how the |case| rule --- in particular, the two requirements for adaptive branches --- are to be incorporated into our derivation format.
Observe that the two requirements can be rewritten as relational inclusions:
\begin{align*}
& |(all(s, v)) ~ (R CAP (NORM M)) s v ~ => ~ (R CAP NormalDomain) (f s v) v| \\[-1ex]
\equiv\quad & |R CAP (NORM M) ~ SUBSETEQ ~ (COM(s v || (R CAP NormalDomain) (f s v) v))| \displaybreak[0] \\
& |(all(s, v)) ~ (R CAP (NORM M)) s v ~ => ~ (all(s')) ~ R' s' (f s v) v ~ => ~ R' s' s v| \\[-1ex]
\equiv\quad & |(COM(s' s v || R' s' (f s v) v)) CAP (COM(_ s v || (R CAP (NORM M)) s v)) ~ SUBSETEQ ~ R'|
\end{align*}
which match the forms of the two inclusions in the consequence rule.
Indeed, if |f|~were a \BiGUL\ operation (symbolising the rerunning of the |case|) such that |(ASSERT Reentry) f (ASSERT Postcondition)|, where the precondition
\savecolumns
\begin{code}
Reentry ~        = ~ (COM(s v | (R CAP NormalDomain) (f s v) v))
\end{code}
states that (before the rerunning) the adapted source |f s v| and the view~|v| should be guaranteed to satisfy |R CAP NormalDomain|, and the postcondition
\restorecolumns
\begin{code}
Postcondition ~  = ~ (COM(s' s v | R' s' (f s v) v))
\end{code}
states that (after the rerunning) |R'|~is established for the updated source~|s'|, the adapted source |f s v|, and the view~|v|, then we could invoke the consequence rule:
\begin{equation}
\begin{array}{l}
|R CAP (NORM M) ~ SUBSETEQ ~ Reentry|
\rulepsep
|(ASSERT Reentry) ~ f ~ (ASSERT Postcondition)|
\rulepsep
|Postcondition CAP (COM(_ s v || (R CAP (NORM M)) s v)) ~ SUBSETEQ ~ R'| \\ \hline
\adjustnorm\phantom{|R CAP (NORM M) ~ SUBSETEQ ~ Reentry| \rulepsep |ASSERT Reentry ~|}
\mathllap{|(ASSERT(R CAP (NORM M))) ~|}
|~ f ~ (ASSERT R')|
\end{array}
\label{eq:adaptation-consequence}
\end{equation}
We therefore use the following derivation format for adaptive branches:
\begin{code}
adaptive M
^  (ASSERT(R CAP (NORM M)))
^  VDOTS
^  (ASSERT Reentry)
^  f
^  (ASSERT Postcondition)
^  VDOTS
^  (ASSERT R')
\end{code}
The way to think about this format is that eventually we want to establish |(ASSERT(R CAP (NORM M)) f (ASSERT R')|, but the actual precondition and postcondition of~|f| are respectively |Reentry|~and~|Postcondition| instead, and hence we should invoke the consequence rule~(\ref{eq:adaptation-consequence}) and prove the two inclusions.
Let us emphasise that assertions in adaptive branches do not really constitute triples, but are merely an organisation of the proof obligations for adaptive branches such that we can work with the proof obligations in the same way as we work with real triples.

\begin{example}[rectangle width updating --- resetting the height]
\label{ex:resetHeight}
Now we can verify the |resetHeight| program as follows, where the precondition is always true and the postcondition says that the consistency will be established and the height will be retained or reset depending on whether the view is consistent or not:
\begin{code}
(ASSERT(_ _))
(ASSERT(COM(_ _) CAP ((COM((w, _) v | w = v)) CUP (COM(_ _))) ))(ASSERTNUMBER *1)
case
^  normal (w, _) v | w = v exit _
^  ^  (ASSERT(COM(_ _) CAP (COM((w, _) v | w = v))))
^  ^  (ASSERT((w, h) v | w = v))
^  ^  (ASSERT((w, h) v | fst (w, h) = v))
^  ^  skip fst
^  ^  (ASSERT((w', h') (w, h) _ | (w', h') = (w, h)))
^  ^  (ASSERT((w', h') (w, h) v | w' = v && (w = v => h' = h) && (w /= v => h' = 0)))(ASSERTNUMBER *3)
^  ^  (ASSERTL((w', h') (w, h) v |
^  ^  (ASSERTR(w' = v && (w = v => h' = h) && (w /= v => h' = 0) && w' = v && (COM(_)) (w', h')))(ASSERTNUMBER *2)
^  adaptive _ _
^  ^  (ASSERT(COM(_ _) CAP ((COM(_ _)) CAP not (COM((w, _) v | w = v)))))
^  ^  (ASSERT((w, _) v | w /= v))(ASSERTNUMBER *8)
^  ^  (ASSERT(_ v | (COM(_ _) (v, 0) v && (COM((w, _) v | w = v)) (v, 0) v)))
^  ^  \ _ v -> (v, 0)
^  ^  (ASSERTL(s' _ v |))
^  ^  (ASSERTR(COM((w', h') (w, h) v | w' = v && (w = v => h' = h) && (w /= v => h' = 0)) s' (v, 0) v))(ASSERTNUMBER *4)
^  ^  (ASSERT((w', h') _ v | w' = v && h' = 0))(ASSERTNUMBER *6)
^  ^  (ASSERT((w', h') (w, h) v | w' = v && (w = v => h' = h) && (w /= v => h' = 0)))(ASSERTNUMBER *7)
(ASSERT((w', h') (w, h) v | w' = v && (w = v => h' = h) && (w /= v => h' = 0)))(ASSERTNUMBER *5)
\end{code}

In this derivation, some assertions (like assertion~1) are given so that it is easier to compare the derivation with the generic |case| rule, but in practice we can often skip these assertions and see that the |case| rule is indeed applicable.
For example, we tend to omit assertion~1 in practice since we can see that the adaptive branch is a catch-all branch; we even tend to omit assertion~2 since we can just check whether assertion~3 covers the extra conditions about the updated source, namely |w' = v && (COM(_)) (w', h')|.

What happens in the adaptive branch is worth tracing.
After the rerunning of the |case| produces an updated source~|s'|, assertion~4 states that the postcondition (assertion~5) holds for~|s'|, the adapted source |(v, 0)|, and the view~|v|.
We can then deduce that the updated width~|w'| is~|v| and, by substituting |(v, 0)| for |(w, h)| in the ``retentive conjunct'' |w = v => h' = h| in assertion~4, that the updated height~|h'| is zero, arriving at assertion~6.
Having |h' = 0| is sufficient for establishing the ``resetting conjunct'' |w /= v => h' = 0| in assertion~7, whose ``retentive conjunct'' |w = v => h' = h| is vacuous due to assertion~8.
\end{example}

\begin{example}[embedding pairs of transformations into \BiGUL] \label{ex:emb}
The |resetHeight| program in fact exhibits a general programming pattern: a |case| with a normal branch accepting consistent states and leaving the source as it is, and an adaptive branch recovering from inconsistency.
We can abstract this pattern to the following |emb| program, which takes a pair of (total) forward and backward transformations and embeds them into \BiGUL:%
%\footnote{This ability can be important when the programmer wishes to reuse some existing transformations or does not want to write a proper BiGUL program (like when it is particularly difficult or when some part of the program needs to be quickly prototyped for requirement testing), and thus deserves some attention regarding what properties |emb| expects its arguments to satisfy.}%
\begin{code}
emb : Eq V => (S -> V) -> (S -> V -> S) -> (S <~ V)
emb g p =  case
           ^  normal s v | g s = v exit _
           ^  ^  skip g
           ^  adaptive _ _
           ^  ^  p
\end{code}
%The `|Eq V|' constraint in the type of |emb| indicates that we need decidable equality on~|V| for the program to be executable.
It is easy to see that |resetHeight = emb fst (\ _ v -> (v, 0))|.
What we proved for |resetHeight| in \autoref{ex:resetHeight} can be generalised to the following triple for |emb g p|, where |g|~is used to define consistency:
\[ |(ASSERT(_ _)) ~ emb g p ~ (ASSERT(s' s v || g s' = v && (g s = v => s' = s) && (g s /= v => s' = p s v)))| \]
Interestingly, to prove this triple, we only require |g|~and~|p| to satisfy \PutGet\ (|(all(s, v)) g (p s v) = v|, which is \autoref{thm:well-behavedness}'s \ref{prop:PutGet} specialised for total functions); \GetPut\ of |emb g p| arises from the logic of |emb| itself and does not depend on |g|~and~|p|.
Indeed, in the case of |resetHeight|, the pair of transformations being embedded satisfies only \PutGet.

On the other hand, if we have both \PutGet\ and \GetPut\ (|all(s) p s (g s) = s|), then we can derive a stronger triple saying that the putback behaviour of |emb g p| completely coincides with~|p|:
\begin{code}
(ASSERT(_ _))
case
^  normal s v | g s = v exit _
^  ^  (ASSERT(s v | g s = v))
^  ^  skip g
^  ^  (ASSERT(s' s _ | s' = s))
^  ^  (ASSERT(s' s _ | s' = p s v && g s' = v))(ASSERTNUMBER *1)
^  adaptive _ _
^  ^  (ASSERT(s v | g s /= v))
^  ^  (ASSERT(s v | g (p s v) = v))(ASSERTNUMBER *2)
^  ^  p
^  ^  (ASSERT(s' s v | s' = p (p s v) v))
^  ^  (ASSERT(s' s v | s' = p s v))(ASSERTNUMBER *3)
(ASSERT(s' s v | s' = p s v))
\end{code}
\GetPut\ is used for assertion~1, and \PutGet\ is used for assertion~2.
Assertion~3 requires the \PutTwice\ property |all(s, v) p (p s v) v = p s v|, which is known to follow from \PutGet\ and \GetPut\ (see, e.g., \citet[Section~3]{Fischer-lens-laws}).
\end{example}

\section{Range Triples and Total Forward Consistency}
\label{sec:range-triples}

We have seen in \autoref{ex:emb} that any pair of transformations satisfying only \PutGet\ can be embedded into \BiGUL.
For example, |resetHeight| in \autoref{ex:resetHeight} can be seen as |emb fst reset| where |reset = \ _ v -> (v, 0)|.
An alternative way to embed |reset| is to express it directly in terms of \BiGUL's constructs:
\begin{code}
alwaysResetHeight : (Nat TIMES Nat) <~ Nat
alwaysResetHeight =  rearrV v -> (v, 0)
                     ^  ^  replace
                     ^  *  replace
\end{code}
The two programs |emb fst reset| and |alwaysResetHeight| have roughly the same putback behaviour, which we can establish using putback triples. On the other hand, in the |get| direction, \autoref{thm:partial-forward-consistency} can tell us that both |GRAPH(get (emb fst reset))| and |GRAPH(get alwaysResetHeight)| are contained in |GRAPH(Just . fst)|.
But in fact, |get (emb fst reset)| can compute successfully on all inputs, whereas |get alwaysResetHeight| can only compute successfully on inputs whose second component is zero (and is usually not what one wants in practice).
This reveals that we still lack the machinery for fully understanding forward behaviour.
What we are missing is the ability to estimate the \emph{domain} of a forward transformation, i.e., the subset of sources on which the forward transformation can compute successfully.
To make such estimates for \BiGUL\ programs, which describe putback transformations, the key insight is that, for a well-behaved pair of |put| and |get|, the domain of |get| coincides with the \emph{range} of |put|, i.e., the subset of sources that can be produced by |put|.%
\footnote{To see the coincidence, observe that \ref{prop:PutGet} (as stated in \autoref{thm:well-behavedness}) can be read roughly as ``if |s'|~is produced by |put b|, i.e., |s'|~is in the range of |put b|, then |get b| will compute successfully on~|s'|, i.e., |s'|~will be in the domain of~|get b|'', and \ref{prop:GetPut} says the converse.}
The problem with |alwaysResetHeight| is now clear: it can only produce the sources whose second component is zero, so |get alwaysResetHeight| can compute successfully only on those sources.
By contrast, |emb fst reset| is capable of producing all possible pairs.
Our way ahead is to develop machinery for making such range estimates reliably, and that machinery is a second set of Hoare-style triples.

%We can easily prove that the putback behaviour of |alwaysResetHeight| coincides with |reset| by deriving the putback triple |(ASSERT(_ _)) alwaysResetHeight (ASSERT(s' _ v || s' = (v, 0)))|; then, by \autoref{thm:well-behavedness}, the |put| and |get| semantics of |alwaysResetHeight| must form a well-behaved pair.
%Let us compare |alwaysResetHeight| and |emb fst reset|:
%\begin{itemize}[leftmargin=*]
%\item With |emb fst reset|, apart from providing |reset|, we also need to provide a forward transformation |fst| and prove \PutGet. In the end we obtain well-behavedness but not precise embedding of |reset|'s behaviour.
%\item With |alwaysResetHeight|, we simply express |reset| in \BiGUL, and obtain the corresponding forward transformation, well-behavedness, and precise embedding.
%\end{itemize}
%It might seem that |alwaysResetHeight| is clearly the better solution, but that is only because we have been looking in the putback direction exclusively.
%In the forward direction, \autoref{thm:partial-forward-consistency} tells us that |(GRAPH(get (emb fst reset)) SUBSETEQ (COM((w, _) v || w = v))| and |(GRAPH(get alwaysResetHeight)) SUBSETEQ (COM((w, 0) v || w = v))|, so both |get (emb fst reset)| and |get alwaysResetHeight| necessarily behave like |fst|.
%But that is not the whole story --- in fact, |get (emb fst reset)| is more versatile than |get alwaysResetHeight|, because the former can compute successfully on all inputs, whereas the latter can only compute successfully on inputs whose second component is zero, and is usually not what one wants in practice.

%The moral of the above story is that we still lack the machinery for understanding forward behaviour, so that we could not see that |alwaysResetHeight| was actually less versatile.
%What helped us to arrive at the right conclusion is the ability to estimate the \emph{domain} of a forward transformation, i.e., the subset of sources on which the forward transformation can compute successfully.
%To make such estimates for \BiGUL\ programs, which describe putback transformations, the key insight is that, for a well-behaved pair of |put| and |get|, the domain of |get| coincides with the \emph{range} of |put|, i.e., the subset of sources that can be produced by |put|.%
%\footnote{To see the coincidence, observe that \ref{prop:PutGet} (as stated in \autoref{thm:well-behavedness}) can be read roughly as ``if |s'|~is produced by |put b|, i.e., |s'|~is in the range of |put b|, then |get b| will compute successfully on~|s'|, i.e., |s'|~will be in the domain of~|get b|'', and \ref{prop:GetPut} says the converse.}
%The problem with |alwaysResetHeight| is now clear: it can only produce the sources whose second component is zero, so |get alwaysResetHeight| can compute successfully only on those sources.
%By contrast, |emb fst reset| is capable of producing all possible pairs.
%Our way ahead is to develop machinery for making such range estimates reliably, and that machinery is a second set of Hoare-style triples.

\subsection{Theory of Range Triples}

\begin{definition}
A \emph{range triple} is a \BiGUL\ program |b : S <~ V| surrounded by two \emph{range assertions}:
\[ |(ASSERTRANGE R) ~ b ~ (ASSERTRANGE P')| \]
where |R : (POWER(S TIMES V))| is the precondition or \emph{input range} (on the original source and the view) and |P' : (POWER S)| is the postcondition or \emph{output range} (on the updated source).
Valid range triples are inductively defined by the proof rules in \autoref{fig:range-proof-rules} (which will be explained in \autoref{sec:range-proof-rules}).
\end{definition}

While the intended interpretation of a range triple for~|b| is about the range of |put b|, we actually need a slightly stronger interpretation about |get b| (to make \autoref{thm:total-forward-consistency} work), as stated by the following soundness and completeness theorem (which is, in a sense, dual to \autoref{thm:putback-soundness-and-completeness}).

\begin{theorem}[soundness and completeness of range triples] \label{thm:range-soundness-and-completeness}
Let |b : S <~ V|, |R : (POWER(S TIMES V))|, and |P' : (POWER S)|.
\[ |(ASSERTRANGE R) ~ b ~ (ASSERTRANGE P')| \IFF |(all(s)) ~ P' s ~ => ~ (some(v)) ~ get b s = Just v ~ && ~ R s v| \PERIOD \]
\end{theorem}

We can recover the intended interpretation of range triples by showing that the right-hand side of \autoref{thm:range-soundness-and-completeness} is equivalent to a statement primarily about |put|, as stated in the following lemma.

\begin{lemma} \label{lem:range-interpretation}
The right-hand side of \autoref{thm:range-soundness-and-completeness} is equivalent to:
\[ (|(all(s')) ~ P' s' ~ => ~ (some(s, v)) ~ R s v ~ && ~ put b s v = Just s'|) \quad|&&|\quad |(GRAPH(get b)) CAP (COM(s _ || P' s)) ~ SUBSETEQ ~ R| \]
\end{lemma}

The left conjunct in \autoref{lem:range-interpretation} is the primary way in which we think about the range triples: if |(ASSERTRANGE R) b (ASSERTRANGE P')| can be derived, then the range of updated sources produced by applying |put b| to those inputs satisfying~|R| will be at least~|P'|.
The right conjunct in \autoref{lem:range-interpretation} says that there is an unintended ``side effect'' when we think about these triples in the putback direction: the input range considered will be forced to include those related by |get| with its domain restricted to~|P'|.
So, for example, we will not be able to deduce |(ASSERTRANGE(m n || m = n + 1)) replace (ASSERTRANGE(_))| even though the left conjunct in \autoref{lem:range-interpretation} is true for this pair of |R|~and~|P'|.
This ``side effect'' normally does not prevent us from deriving range triples, though, since preconditions are normally larger than consistency relations, which in turn contain the graphs of |get| transformations.

Back in \autoref{sec:putback-triples}, where we only had putback triples, \autoref{thm:partial-forward-consistency} only enabled us to understand the forward behaviour of \BiGUL\ programs to a limited extent.
Now supplemented with range triples, we can prove a stronger and satisfactory result.

\begin{theorem}[total forward consistency] \label{thm:total-forward-consistency}
Let |b : S <~ V|, |R : (POWER(S TIMES V))|, |C : (POWER(S TIMES V))|, and |P' : (POWER S)|.
\begin{align*}
& \IF |(ASSERT R) ~ b ~ (ASSERT(s' _ v || C s' v))| \AND |(ASSERTRANGE R) ~ b ~ (ASSERTRANGE P')| \\
& \THEN |(all(s)) ~ P' s ~ => ~ (some(v)) ~ get b s = Just v ~ && ~ C s v| \PERIOD
\end{align*}
\end{theorem}

\begin{proof}
Suppose that |P'|~holds for a source~|s|.
By the range triple and \autoref{thm:range-soundness-and-completeness}, |get b s| will compute successfully to some view~|v| such that |R s v| holds, making |s|~and~|v| fall into |(GRAPH(get b)) CAP R|.
The putback triple and \autoref{thm:partial-forward-consistency} can then take over and establish |C s v| as required.
\end{proof}

\autoref{thm:total-forward-consistency} tells us that, by supplementing a putback triple for~|b| with a range triple with the same precondition, we can know on which subset of sources |get b| will compute successfully and that the behaviour of |get b| will conform to the consistency relation stated in the putback triple.

In summary, now we have enough machinery to tell us all we want to know about the bidirectional behaviour of a \BiGUL\ program:
By deriving a putback triple |(ASSERT R) b (ASSERT(s' s v || C s' v && R' s' s v))| to reason about the behaviour of~|b|, we know that |put b| will compute successfully on~|R|, establish consistency~|C|, and have retentive behaviour~|R'|.
Then, by additionally deriving a range triple |(ASSERTRANGE R) b (ASSERTRANGE P')| to estimate the range of~|b|, we know that |get b| will compute successfully on~|P'| and conform to the same consistency relation~|C| established by |put b|.
Notably, as we will see next, derivations of range triples are usually significantly easier than derivations of putback triples, so in practice there is usually not much more work to do than deriving putback triples.

%We will write
%\[ |(ASSERT R) ~ b ~ (ASSERT R') (ASSERTRANGE P)| \quad\text{as an abbreviation of}\quad |(ASSERT R) ~ b ~ (ASSERT R') ~ ~ && ~ ~ (ASSERTRANGE R) ~ b ~ (ASSERTRANGE P)| \]

\subsection{The Range Proof Rules}
\label{sec:range-proof-rules}

\begin{figure}

$\begin{array}{c}
\hline
|(ASSERTRANGE EMPTY) ~ fail ~ (ASSERTRANGE EMPTY)|
\end{array}$
\rulehsep
$\begin{array}{c}
\hline
|(ASSERTRANGE(s v || s = v)) ~ replace ~ (ASSERTRANGE _)|
\end{array}$
\rulehsep
$\begin{array}{c}
\hline
|(ASSERTRANGE(s v || f s = v)) ~ skip f ~ (ASSERTRANGE _)|
\end{array}$

\rulevsep

$\begin{array}{c}
|(ASSERTRANGE L) ~ l ~ (ASSERTRANGE P')| \rulepsep
|(ASSERTRANGE R) ~ r ~ (ASSERTRANGE Q')| \\ \hline
|(ASSERTRANGE(L * R)) ~ l * r ~ (ASSERTRANGE(P' * Q'))|
\end{array}$
\rulehsep
$\begin{array}{l}
|R CAP (COM(s _ || Q' s)) ~ SUBSETEQ ~ T| \rulepsep
|{-"\assertrange{\awa{T}{R}}\;"-} ~ b ~ {-"\;\assertrange{\awa{Q^\prime}{P^\prime}}"-}| \rulepsep
|Q' ~ SUBSETEQ ~ P'| \\ \hline
\phantom{|R CAP (COM(s _ || Q' s)) ~ SUBSETEQ ~ T| \rulepsep} |{-"\assertrange{T}\;"-} ~ b ~ {-"\;\assertrange{Q^\prime}"-}|
\end{array}$

\rulevsep

$\begin{array}{c}
|(ASSERTRANGE(s wpat || R s (ENV(wpat)))) ~ b ~ (ASSERTRANGE P')| \\ \hline
\adjustrearr |(ASSERTRANGE(s vpat || R s (ENV(vpat)))) ~ rearrV vpat -> wpat INNER b ~ (ASSERTRANGE P')|
\end{array}$

\rulevsep

$\begin{array}{c}
|(ASSERTRANGE(tpat v || R (ENV(tpat)) v)) ~ b ~ (ASSERTRANGE(tpat || P' (ENV(tpat))))| \\ \hline
\adjustrearr |(ASSERTRANGE(spat v || R (ENV(spat)) v)) ~ rearrS spat -> tpat INNER b ~ (ASSERTRANGE(spat || P' (ENV(spat))))|
\end{array}$

\rulevsep

$\begin{array}{cl}
|all(n = (normal M exit E INNER b) `elem` bs)| \\
|(ASSERTRANGE(R CAP (NORM M))) ~ b ~ (ASSERTRANGE P'_n)|
& |where| \\ \cline{1-1}
|(ASSERTRANGE R) ~ case INNER bs ~ (ASSERTRANGE(CaseRange))|
& \quad |CaseRange = BIGCUP ~ [ P'_n CAP (NORM E) || n = (normal M exit E INNER b) `elem` bs ]|
\end{array}$

\caption{Range proof rules}
\label{fig:range-proof-rules}

\end{figure}

%\begin{lemma} \label{lem:branch-range-containment}
%Let |b : S <~ V|, |R : (POWER(S TIMES V))|, |P' : (POWER S)|, and |Q' : (POWER S)|.
%\[ \IF |(ASSERT R) ~ b ~ (ASSERT(s' _ _ || Q' s')) (ASSERTRANGE P')| \THEN |P' SUBSETEQ Q'| \PERIOD \]
%\end{lemma}

The range proof rules are shown in \autoref{fig:range-proof-rules}.
The most interesting rule is probably the consequence rule (the right one in the second row), whose direction is just the opposite of the putback consequence rule given in \autoref{fig:putback-proof-rules}.
An explanation is that the ultimate interpretation of range triples, as stated by \autoref{thm:range-soundness-and-completeness}, is about forward behaviour, and the output/input range in a range triple in fact serves the role of precondition/postcondition for the forward transformation.
But, interestingly, the consequence rule can also be understood in the putback direction:
If |(ASSERTRANGE R) b (ASSERTRANGE P')| has been established, meaning that the inputs in~|R| can induce everything in~|P'| through the execution of~|b|, then a larger input range~|T| can still induce everything in~|P'|, or indeed everything in any output range~|Q'| smaller than~|P'|.
In fact, |T|~is not necessarily larger than~|R|: if what we eventually target is a smaller output range, then we will be allowed to also shrink the input range --- as stated in the consequence rule, we are allowed to use~|Q'| to constrain the sources in the input range.
Since the direction of the range consequence rule is the opposite of the putback one, when deriving a range triple using the consequence rule in our derivation format, logical implications go upwards, and we can use the postconditions for a node as additional premises when proving implications between preconditions for the same node, opposite to what we do in putback derivations.

Other rules should be largely intuitive.
The |fail| rule has the empty predicate as its output range since |fail| can never produce anything (and its input range can be any relation because of the consequence rule).
The |replace| rule says that |replace| can produce everything as long as the input range is large enough --- because of the ``side effect'' explained below \autoref{lem:range-interpretation}, the input range has to be large enough to include the graph of |replace|'s forward semantics, which is the identity transformation.
The |skip| rule has the same precondition as its putback counterpart and says that |skip| can produce everything.
The product and rearrangement rules are analogous to their putback counterparts.
For |case|, only normal branches matter since execution of |case| always ends in a normal branch.
We estimate an output range~|P'_n| for the body of every normal branch~|n|, and the estimated output range for that branch is |P'_n|~intersected with the actual exit condition, since only outputs satisfying the actual exit condition can be produced.
The estimated output range for the entire |case| is then the union of the estimated output ranges for all the normal branches.

\begin{example}[embedding pairs of transformations in \BiGUL] \label{ex:emb-range}
As we mentioned, derivations of range triples can be very straightforward in simple cases.
In the case of |emb|, for example, we can effortlessly prove that it produces everything:
\begin{code}
(ASSERTRANGE(_ _))
case
^  normal s v | g s = v exit _
^  ^  (ASSERTRANGE(s v | g s = v))
^  ^  skip g
^  ^  (ASSERTRANGE(_))
^  adaptive _ _
^  ^  p
(ASSERTRANGE(_))
\end{code}
\end{example}

\begin{example}[rectangle width updating --- always resetting the height] \label{ex:alwaysResetHeight}
Verifying the range of |alwaysResetHeight| is a more interesting example, where we will see how a non-trivial output range can be derived with the help of the consequence rule:
\begin{code}
(ASSERTRANGE(_ _))
rearrV v -> (v, 0)
^  (ASSERTRANGE(_ (_, 0)))
^  ^   (ASSERTRANGE(_ _))
^  ^   (ASSERTRANGE(w v | w = v))
^  ^   replace
^  ^   (ASSERTRANGE(_))
^  *   (ASSERTRANGE(_ 0)) (ASSERTRANGENUMBER *3)
^  ^   (ASSERTRANGE(h v | h = v)) (ASSERTRANGENUMBER *1)
^  ^   replace
^  ^   (ASSERTRANGE(_)) (ASSERTRANGENUMBER *2)
^  ^   (ASSERTRANGE(0)) (ASSERTRANGENUMBER *4)
^  (ASSERTRANGE((_, 0)))
(ASSERTRANGE((_, 0)))
\end{code}
The interesting part is the second |replace|, for which we first establish the input and output ranges as assertions 1~and~2 according to the |replace| rule.
However, because of the outer |rearrV|, the views in the actual input range for the second |replace| are restricted to zero, as stated by assertion~3, which does not contain assertion~1.
We therefore need to shrink our estimate of the output range of |replace| to just zero (assertion~4) to allow us to also restrict the views in the input range to zero.
Logically, assertions 1~and~4 together indeed imply assertion~3, adhering to the consequence rule.
\end{example}

\section{Recursion}
\label{sec:recursion}

\BiGUL\ is designed datatype-generically~\citep{Gibbons-DGP} to work with inductive data structures.
A lot of recursive programs processing inductive data have been written using the \Haskell\ port of \BiGUL, and our Hoare-style logic would not be useful at all if we could not reason about such recursive \BiGUL\ programs.
For example, let us take a peek at the key-based list alignment program |keyAlign| in \autoref{fig:keyAlign}, which we will verify in \autoref{sec:key-based-alignment}.
All we need to care about in regard to |keyAlign| now is its recursive structure.
Both the source and view are lists, and in the second branch of the |case|, they are both non-empty.
Inside the branch, each of them is rearranged into a pair of its head and tail, and we recursively invoke the program to process the tails.
Intuitively, we know that this program terminates for any input because the size of the initial source and view is strictly larger than the size of the source and view at the point of the recursive invocation.
We will need to incorporate this size-based termination argument into our proof rules for recursive programs, and show that the rules are sound.

There is difficulty dealing with recursive programs in the \Agda\ formalisation underlying this paper, though.
Observe that the program structure of |keyAlign| is infinite, which is fine in \Haskell; in the \Agda\ formalisation, however, \BiGUL\ programs are modelled inductively and are necessarily finite.
One possible solution is to redefine \BiGUL\ programs coinductively and bring in the partiality monad~\citep{Capretta-general-recursion} to model non-termination in \Haskell, but this means abandoning most (if not all) of the previous formalisation effort.
Another possible solution is to stay with inductive \BiGUL\ programs and introduce a ``terminating fixed-point'' which can decide, for every input, how many times the body of a fixed-point should be expanded, thereby circumventing the modelling of infinite program structures.
This approach will be relevant in a constructive setting, but we anticipate that there will be extra constructivity requirements that are not relevant for the \Haskell\ port of \BiGUL, in which most (recursive) \BiGUL\ programs are written.
Since what we aim at in this paper is not thorough formalisation but a semi-formal reasoning framework for the working \BiGUL\ programmer, we will develop just enough theory to justify our rules for reasoning about recursive programs, and refrain from delving into coinductiveness or constructive termination.

Let |b : S <~ V| be a recursive program of the form |b = f b| where |f : (S <~ V) -> (S <~ V)| is the usual non-recursive function defining the body of~|b|, and suppose that we want to verify that |b|~can successfully turn any input satisfying a precondition~|R| into an output satisfying a postcondition~|R'|.
We cannot hope to establish |(ASSERT R) b (ASSERT R')| (although we will abuse this notation in \autoref{sec:key-based-alignment}) since putback triples are defined for finite programs, whereas |b|~is infinite.
Instead, when we say in this paper that we are verifying~|b|, what we precisely mean is verifying the behaviour of all \emph{finite expansions} of its body~|f|, where finite expansions are defined by:
\begin{code}
expand : Nat -> ((S <~ V) -> (S <~ V)) -> (S <~ V)
expand zero     f = fail
expand (suc n)  f = f (expand n f)
\end{code}
The basic idea is to prove something about~|f| like:
\begin{equation}
|(all(rec : S <~ V))| \quad |(ASSERT R) ~ rec ~ (ASSERT R')| \quad|=>|\quad |(ASSERT R) ~ f rec ~ (ASSERT R')|
\label{prop:basic-proof-idea}
\end{equation}
which can then be iterated to produce |(ASSERT R) expand n f (ASSERT R')| for any~|n| --- the base case is |(ASSERT R) fail (ASSERT R')|, which implies |(ASSERT R) f fail (ASSERT R')|, and then |(ASSERT R) f (f fail) (ASSERT R')|, etc.
This idea cannot be directly valid, however, since in general only a subset of~|R| can be successfully processed by a finite expansion of~|f| (whose execution can be thought of as executing~|b| but allowing recursive invocations only to a certain depth).
%or otherwise we would be able to prove that any finite expansion can successfully process the entire~|R|.
We thus introduce a function of type |S -> V -> Nat| for measuring the size of the source and view in assertions, and include size restrictions in the preconditions for the finite expansions, leading to the following theorem.

\begin{theorem}[finite expansion of putback triples] \label{thm:putback-finite-expansion}
Let |f : (S <~ V) -> (S <~ V)|, |R : (POWER(S TIMES V))|, |R' : (POWER(S TIMES S TIMES V))|, and |measure : S -> V -> Nat|.
If
\begin{align}
|(all(n, rec))|\quad & |((all m) ~ (ASSERT(R CAP (COM(s v || measure s v = m && m < n)))) ~ rec ~ (ASSERT R'))| \nonumber \\
& \quad|=>|\quad |(ASSERT(R CAP (COM(s v || measure s v = n)))) ~ f rec ~ (ASSERT R')| \tag{\PutbackRecursion} \label{prop:PutbackRecursion}
\end{align}
then:
\[ |(all(l, n)) ~ n <= l ~ =>| \quad |(ASSERT(R CAP (COM(s v || measure s v = n)))) ~ expand (suc l) f ~ (ASSERT R')| \]
\end{theorem}

\ref{prop:PutbackRecursion} will be the proof rule we use for reasoning about the putback behaviour of recursive programs.
It combines the basic proof idea~(\ref{prop:basic-proof-idea}) with the size-based termination argument given in the beginning of this section: in the precondition for |f rec|, the size of the input source and view is bound to a logic variable~|n|, and we can make recursive invocations wherever the size~|m| of the current source and view is strictly less than~|n|.
The soundness of \ref{prop:PutbackRecursion} is justified by \autoref{thm:putback-finite-expansion}, whose conclusion implies that any input in~|R| can be successfully turned into an output in~|R'| as long as |f|~is expanded enough times.
%We again omit the proof of the theorem (which is by nested induction on |l|~and~|n|) from the presentation.

Analogously, we have a \ref{prop:RangeRecursion} rule for estimating the output ranges of recursive programs.

\begin{theorem}[finite expansion of range triples] \label{thm:range-finite-expansion}
Let |f : (S <~ V) -> (S <~ V)|, |R : (POWER(S TIMES V))|, |P' : Nat -> (POWER S)|, and |measure : S -> V -> Nat|.
If
\begin{align}
|(all(n, rec))| \quad & |((all m) ~ (ASSERTRANGE(R CAP (COM(s v || measure s v = m)))) ~ rec ~ (ASSERTRANGE(P' m CAP (COM(_ || m < n)))))| \nonumber \\
& \quad|=>|\quad |(ASSERTRANGE(R CAP (COM(s v || measure s v = n)))) ~ f rec ~ (ASSERTRANGE(P' n))| \tag{\RangeRecursion} \label{prop:RangeRecursion}
\end{align}
then:
\[ |(all(l, n)) ~ n <= l ~ =>| \quad |(ASSERTRANGE(R CAP (COM(s v || measure s v = n)))) ~ expand (suc l) f ~ (ASSERTRANGE(P' n))| \]
\end{theorem}

The \ref{prop:RangeRecursion} rule instructs us to derive an output range |P' n| that can depend on the logic variable~|n| bound to the size of the input source and view in the precondition.
(For example, the range triple we will derive for |keyAlign| is |(ASSERTRANGE(_ vs || length vs = n)) keyAlign ... (ASSERTRANGE(ss || length ss = n))|.)
Recursive invocations can be made in the derivation, and the estimated output range for a recursive invocation is |P' m| where |m|~is the size of the current source and view, provided that |m|~is strictly less than~|n| --- otherwise, the estimated output range will be empty.
The conclusion of \autoref{thm:range-finite-expansion} justifies the soundness of \ref{prop:RangeRecursion}, as it implies that every output in $\bigcup_{|n : Nat|} |P' n|$ can be produced from some input of the right size in~|R| as long as |f|~is expanded enough times.

Having the two recursion rules, we are now ready to verify |keyAlign|.
%\todo{\autoref{thm:total-forward-consistency} and other theorems also work semantically}

\section{Verifying Key-Based List Alignment}
\label{sec:key-based-alignment}

\begin{figure}
\flushleft
\begin{code}
keyAlign : Eq K => (S -> K) -> (V -> K) -> (S <~ V) -> (V -> S) -> ([S] <~ [V])
keyAlign ks kv b c =
  case
  ^  normal [] [] exit []
  ^  ^  rearrV [] -> ()
  ^  ^  ^   skip const ()
  ^  normal (s :: _) (v :: _) | ks s = kv v exit (_ :: _)
  ^  ^  rearrS (s :: ss) -> (s, ss)
  ^  ^  ^  rearrV (v :: vs) -> (v, vs)
  ^  ^  ^  ^  ^  b
  ^  ^  ^  ^  *  keyAlign ks kv b c
  ^  adaptive (_ :: _) []
  ^  ^  \ _ _ -> []
  ^  adaptive ss (v :: _) | kv v `elem` map ks ss
  ^  ^  \ ss (v :: _) -> extract ks kv v ss
  ^  adaptive _ (_ :: _)
  ^  ^  \ ss (v :: _) -> c v :: ss
  where
    extract : Eq K => (S -> K) -> (V -> K) -> V -> [S] -> [S]
    extract ks kv v (s :: ss) = if ks s == kv v  then  s :: ss
                                                 else  let  (s' :: ss') = extract ks kv v ss
                                                       in   s' :: s :: ss'
\end{code}
\caption{Key-based list alignment in \BiGUL}
\label{fig:keyAlign}
\end{figure}

Alignment is a representative problem for bidirectional transformations~\citep{Bohannon-Boomerang,Barbosa-matching-lenses,Diskin-delta-asymmetric,Pacheco-delta-lenses,Voigtlander-shape-plug-ins,McKinna-proof-relevant-bisimulations}.
In this paper, we focus on the specialised (and asymmetric) setting where both the source and view are lists, which are consistent exactly when they have the same length and an element-level consistency relation is satisfied by each pair of the source and view elements at the same position.
%(for example, the source elements can be rectangles and the view elements are their widths).
View elements may be inserted, deleted, modified, or reordered.
To put the updated view list back into the source list, we need to align the two lists, i.e., decide for each view element to which source element it corresponds (if any), before we can invoke an element-level consistency restorer on the right pairs of source and view elements.

Several variants of list alignment have been implemented in \BiGUL~\citep{Zan-Brul, Mendes-delta-alignment}.
In this paper we choose to verify a variant that is non-trivial and yet not overly complicated: key-based alignment, of which an implementation was presented and explained with a concrete scenario by
\citet[Section~6.2]{Hu-BiGUL-tutorial}.
Their program |keyAlign| is shown in \autoref{fig:keyAlign}.
The types of source and view elements are |S|~and~|V| respectively.
The program takes two functions |ks : S -> K| and |kv : V -> K| as arguments, which are used to extract a key value of type~|K| from every source or view element, and the type~|K| should support decidable equality.
Two more arguments |b|~and~|c| are needed to deal with two of the three possible situations that can result from an alignment:
\begin{itemize}[leftmargin=*]
\item A view element~|v| is deemed to correspond to a source element~|s| only if their keys match, i.e., |ks s = kv v|; an element-level synchroniser |b : S <~ V| will then be invoked on this pair of source and view elements.
\item If no source element has the same key as a view element, a function |c : V -> S| will be used to create a temporary corresponding source; this temporary source will then be fully synchronised with the view using~|b|.
\item A source element will be deleted if there is no corresponding view element.
\end{itemize}

Here is a quick overview of the program:
The first branch is the base case.
The second branch deals with ``happy coincidences'': the head elements in the source and view lists match, so we can simply synchronise the heads and recursively process the tails.
The third branch deletes everything in the source when the view is empty.
The fourth branch is the most interesting: the head view element~|v| has a corresponding source element (which is not at the head position), so we |extract| the first source element with the same key as~|v| and put it at the head (intending to re-enter the second branch afterwards).
When there is no source element corresponding to the head view element, the fifth and last branch uses~|c| to create a temporary corresponding source element.
Note that the program uses some partial functions, which are fine in \Haskell\ but not in \Agda: |extract|, for example, misses two cases for empty source lists, and these cases have to be added for verification in \Agda. These missing cases are irrelevant, however, since |keyAlign| does not invoke |extract| on empty source lists.


To verify |keyAlign|, we need to make some assumptions about its arguments.
For simplicity, we assume that |b|~can compute successfully for any pair of source and view elements with the same key; also, |b|~should guarantee that the updated source and the view will have the same key, apart from any other postcondition |R' : (POWER(S TIMES S TIMES V))| it can establish.
As a putback triple:
\[ |(ASSERT(s v || ks s = kv v)) ~ b ~ (ASSERT(R' CAP (COM(s' _ v || ks s' = kv v))))| \]
We will abbreviate |R' CAP (COM(s' _ v || ks s' = kv v))| as~|T'|.
For the source-creating function~|c|, since a created source will be further processed by~|b|, we require the key of the created source to be the same as that of the view:
\[ |(all(v)) ~ ks (c v) = kv v| \]
We can then derive, for all~|n|:
\begin{code}
(ASSERT(_ vs | length vs = n)) ~ keyAlign ks kv b c ~ (ASSERT(ss' ss vs | (some(~ ss'')) (STAR T') ss' ss'' vs && Retentive ss vs ss''))
\end{code}
In the precondition, we use the length of the view list as the termination measure, but otherwise impose no restrictions on the source and view lists.
In the postcondition, the relation |(STAR T') : (POWER([S] TIMES [S] TIMES [V]))| is defined inductively by the following two rules:
\begin{code}
(STAR T')  []           []             []
(STAR T')  (s' :: ss')  (s'' :: ss'')  (v :: vs) ~ <== ~ T' s' s'' v &&  (STAR T') ss' ss'' vs
\end{code}
The postcondition thus guarantees that the updated source list |ss'| will have the same length as |vs|, and for each pair of source element~|s'| in~|ss'| and view element~|v| in~|vs| at the same position, |T'| will be established for |s'|,~some source element~|s''|, and~|v|.
The elements~|s''| are collected into a list~|ss''|, and |Retentive ss vs ss''| says that |ss''|~contains those source elements in~|ss| that correspond to some view element in~|vs|.
This |Retentive| relation turns out to be slightly tricky to define, especially when we do not require that keys in a list are all unique; our definition says that if a key appears |n|~times in the view list, then the first |n|~elements with that key in the original source list will be retained.

Due to space restrictions, we only sketch the verification of the second normal branch and the second adaptive branch.
%(The complete, \Agda-checked verification is provided in the supplementary material.)
The assertions for the second normal branch are as follows, where we omit the invocations of the |rearrS|, |rearrV|, and product rules since they are straightforward in this case:
\begin{code}
normal (s :: _) (v :: _) | ks s = kv v exit (_ :: _)
^  (ASSERT((s :: _) (v :: vs) | 1 + length vs = n && ks s = kv v)) (ASSERTNUMBER *6)
^  rearrS (s :: ss) -> (s, ss)
^  ^  rearrV (v :: vs) -> (v, vs)
^  ^  ^  ^  (ASSERT(s v | ks s = kv v))
^  ^  ^  ^  b
^  ^  ^  ^  (ASSERT T')
^  ^  ^  *  (ASSERT(_ vs | 1 + length vs = n)) (ASSERTNUMBER *1)
^  ^  ^  ^  (ASSERT(_ vs | length vs = pred n && pred n < n)) (ASSERTNUMBER *2)
^  ^  ^  ^  keyAlign ks kv b c
^  ^  ^  ^  (ASSERT(ss' ss vs | (some(~ ss'')) (STAR T') ss' ss'' vs && Retentive ss vs ss'')) (ASSERTNUMBER *3)
^  (ASSERT((s' :: ss') (s :: ss) (v :: vs) | T' s' s v && (some(~ ss'')) (STAR T') ss' ss'' vs && Retentive ss vs ss'')) (ASSERTNUMBER *4)
^  (ASSERTL((s' :: ss') ss (v :: vs) |))
^  (ASSERTR(some(~ ss'') (STAR T') (s' :: ss') ss'' (v :: vs) && Retentive ss (v :: vs) ss'' && ks s' = kv v)) (ASSERTNUMBER *5)
\end{code}
We first look at how the \ref{prop:PutbackRecursion} rule is applied.
Assertion~1 is the actual precondition for the recursive invocation, and we rewrite it into assertion~2, saying that the length of the view list at this point is |pred n|, which is strictly less than~|n| since assertion~1 says that |n|~is a successor.
(The predecessor function is defined by |pred zero = zero| and |pred (suc n) = n|, so |pred n| is not necessarily less than~|n|.)
The recursive invocation will thus succeed and establish assertion~3.
For the postconditions, the |rearrS|, |rearrV|, and product rules give us assertion~4, while we need to prove assertion~5.
The last conjunct |ks s' = kv v| in assertion~5 is part of |T' s' s v| in assertion~4 by definition.
From |T' s' s v| and |(some(~ ss'')) (STAR T') ss' ss'' vs| in assertion~4, we see that we should use |s :: ss''| as the new |ss''| in assertion~5.
We are left to prove |Retentive (s :: ss) (v :: vs) (s :: ss'')| (since |ss| in assertion~5 is |s :: ss| in assertion~4), which is implied by |Retentive ss vs ss''| in assertion~4 and |ks s = kv v| in assertion~6.

Now we turn to the second adaptive branch:
\begin{code}
adaptive ss (v :: _) | kv v `elem` map ks ss
^  (ASSERT(ss (v :: _) | kv v `elem` map ks ss)) (ASSERTNUMBER *1)
^  (ASSERT(ss (v :: vs) | (COM((s :: _) (v :: _) | ks s = kv v)) (extract ks kv v ss) (v :: vs))) (ASSERTNUMBER *2)
^  \ ss (v :: _) -> extract ks kv v ss
^  (ASSERTL(ss' ss (v :: vs) |))
^  (ASSERTR(COM(ss' ss vs | (some(~ ss'')) (STAR T') ss' ss'' vs && Retentive ss vs ss'') ss' (extract ks kv v ss) (v :: vs))) (ASSERTNUMBER *3)
^  (ASSERT(ss' ss vs | (some(~ ss'')) (STAR T') ss' ss'' vs && Retentive ss vs ss'')) (ASSERTNUMBER *4)
\end{code}
Assertion~1 (where we omit the negations of the previous main conditions) implies assertion~2, which is the condition for re-entering the second normal branch: the source list~|ss| must be non-empty so that |extract ks kv v ss| will successfully produce a non-empty list, whose head will then have the same key as the head view element~|v|.
After adaptation, the rerunning of the |case| establishes assertion~3, which should be shown to imply assertion~4, the final postcondition.
Assertion~3 says that |STAR T'| holds for the updated source list |ss'|, some list |ss''| of source elements, and the view list, and we can directly use |ss''| as the witness and establish the first conjunct in assertion~4.
Assertion~3 also says that |ss''| retains certain elements from the adapted source list, which is just the original source list with its first source element having key |kv v| moved to the head position, so we know that |ss''| retains the same elements in the original source list as well.
This is an illustrative example showing that adaptation should be done cautiously to maintain sufficient similarity between the adapted source and the original source, or otherwise it can be immensely difficult to prove the implication from the adapted postcondition to the final postcondition.

We should not forget to derive a range triple for |keyAlign|.
For simplicity, let us derive:
\begin{code}
(all(n)){-"\quad"-} (ASSERTRANGE(_ vs | length vs = n)) ~ keyAlign ks kv b c ~ (ASSERTRANGE(ss | length ss = n))
\end{code}
assuming:
\begin{code}
(ASSERTRANGE(s v | ks s = kv v)) ~ b ~ (ASSERTRANGE(_))
\end{code}
That is, if |b|~is capable of producing everything, then |keyAlign ks kv b c| can also produce everything.
If |T' SUBSETEQ (COM(s' _ v || C s' v))| for some element-level consistency relation |C : (POWER(S TIMES V))|, then by \autoref{thm:total-forward-consistency} we know that for any source list, |get (keyAlign ks kv b c)| will successfully produce a view list of the same length, and each pair of source and view elements at the same position will satisfy~|C|.
For the derivation, again due to space restrictions we can only give a quick sketch:
We only need to derive ranges for the two normal branches.
The output range of the first branch can be derived as |COM([] || 0 = n)| --- that is, the branch can produce empty lists when |0 = n|; as for the output range of the second branch, we can derive |COM((_ :: ss) || 1 + length ss = n)|.
Their union is the output range of the entire |case|, and is indeed |COM(ss || length ss = n)|.

%\begin{code}
%keyAlign ks kv b c =
%  (ASSERTRANGE(_ vs | length vs = n))
%  case
%  ^  normal [] [] exit []
%  ^  ^  (ASSERTRANGE([] [] | 0 = n))
%  ^  ^  rearrV [] -> ()
%  ^  ^  ^   (ASSERTRANGE([] () | 0 = n))
%  ^  ^  ^   (ASSERTRANGE(ss v | const () ss = v))
%  ^  ^  ^   skip const ()
%  ^  ^  ^   (ASSERTRANGE([] | 0 = n))
%  ^  normal (s :: _) (v :: _) | ks s = kv v exit (_ :: _)
%  ^  ^  (ASSERTRANGE((s :: _) (v :: vs) | ks s = kv v && 1 + length vs = n))
%  ^  ^  rearrS (s :: ss) -> (s, ss)
%  ^  ^  ^  (ASSERTRANGE((s, _) (v :: vs) | ks s = kv v && 1 + length vs = n))
%  ^  ^  ^  rearrV (v :: vs) -> (v, vs)
%  ^  ^  ^  ^  (ASSERTRANGE((s, _) (v, vs) | ks s = kv v && 1 + length vs = n))
%  ^  ^  ^  ^  ^   (ASSERTRANGE(s v | ks s = kv v))
%  ^  ^  ^  ^  ^   b
%  ^  ^  ^  ^  ^   (ASSERTRANGE(_))
%  ^  ^  ^  ^  *   (ASSERTRANGE(_ vs | 1 + length vs = n))
%  ^  ^  ^  ^  ^   (ASSERTRANGE(_ vs | length vs = prev n))
%  ^  ^  ^  ^  ^   keyAlign ks kv b c
%  ^  ^  ^  ^  ^   (ASSERTRANGE(ss | length ss = prev n && prev n < n))
%  ^  ^  ^  ^  ^   (ASSERTRANGE(ss | 1 + length ss = n))
%  ^  ^  ^  ^  (ASSERTRANGE((_, ss) | 1 + length ss = n))
%  ^  ^  ^  (ASSERTRANGE((_, ss) | 1 + length ss = n))
%  ^  ^  (ASSERTRANGE((_ :: ss) | 1 + length ss = n))
%  ^  VDOTS
%  (ASSERTRANGE(COM([] | 0 = n) CUP (COM((_ :: ss) | 1 + length ss = n))))
%  (ASSERTRANGE(ss | length ss = n))
%\end{code}

\section{Discussion}
\label{sec:discussion}

\varparagraph{How expressive is \BiGUL\ (especially compared with existing languages)?}
The expressive power of the version of \BiGUL\ used in this paper mainly stems from its |case| construct, which has gone beyond \varcitet{Foster-lenses}{'s} ``general conditional'' and allows, in particular, key-based list alignment to be implemented using only simple and general-purpose primitives for the first time.
(In the original \BiGUL~\citep{Ko-BiGUL}, the case analysis constructs were essentially the same as \citeauthor{Foster-lenses}'s conditionals, and key-based list alignment had to be provided as an extra and complex primitive.)

Regarding alignment, \varcitet{Barbosa-matching-lenses}{'s} ``matching lenses'' offer several sophisticated matching strategies, some of which can be hard to implement ``nicely'' in \BiGUL\ so far.
However, matching lenses are special-purpose and require the invention of dedicated laws, and the essential components are built from scratch, whereas \BiGUL\ is designed with the ultimate aim of expressing all lenses using just a fixed set of simple primitives, like what we can do in general-purpose languages.
In particular, we can program alignment in \BiGUL\ without having to bake special-purpose concepts like \citeauthor{Barbosa-matching-lenses}'s ``chunks'', ``rigid complements'', ``resources'' etc into the language.

While seemingly simple, \BiGUL\ has been successfully employed in several practical scenarios, including web server configuration adaptation~\citep{Colson-BiGUL-configuration}, parsing and reflective printing~\citep{Zhu-BiYacc}, synchronisation of feature configurations and use cases~\citep{Zhao-BiGUL-feature-models-use-cases}, and synchronisation of executable programs and proof scripts~\citep{Kinoshita-bidirectional-certified-programming}.

\varparagraph{\BiGUL\ claims to be ``putback-based'' but is still a lens language. Is there really a fundamental difference between \BiGUL\ and previous ``|get|-based'' lens languages?}
Regarding language definition, \BiGUL\ programs denote lenses and have to be defined in both directions, exactly the same as other lens languages.
It is when it comes to \emph{using} the lenses that the distinction between the |get|- and |put|-based approaches becomes meaningful.
The majority of lens languages are |get|-based, as explained by \citet{Foster-thesis} below his Lemma~2.2.6:
`Lens programmers often feel like they are writing the forward transformation (because the names of primitives typically connote the forward transformation) and getting the backward transformation ``for free''\,'.
\citet{Matsuda-applicative-BX}, for example, explicitly state that their language adopts this design.
\citet{Foster-lenses} also clearly show in their Figure~8 that their lens programs are supposed to be constructed like writing |get|, and \varcitet{Bohannon-relational-lenses}{'s} relational lenses are written like database queries, which are |get| transformations.
Their programs can be (and are usually) enriched with putback information to allow more control, but that makes constructing and understanding the programs more awkward (see the next paragraph).
By contrast, \BiGUL's putback-based design lets the programmer construct programs purely in the |put| direction.
The Hoare-style logic helps to clearly distinguish the two approaches for the first time: it is possible to precisely reason about bidirectional behaviour purely in the |put| direction, whereas it is unthinkable that the same can be achieved in the |get| direction.
This might explain that there is only one comparable (but still much less powerful) reasoning framework: the totality lemmas of \citet{Foster-lenses}, which can only establish properties equivalent to triples of the form |(ASSERTRANGE(_ _)) b (ASSERTRANGE P)| and |(ASSERT(s v || P s && Q v)) b (ASSERT(_ _ _))| where |P : (POWER S)| and |Q : (POWER V)|.

\varparagraph{Didn't some |get|-based approaches also offer the ability to control putback behaviour? Why switch to the putback-based approach?}
To name a few, the ``fixup functions'' in \varcitet{Foster-lenses}{'s} ``general conditionals'' (for branch switching), the parameters of \varcitet{Bohannon-relational-lenses-tech-report}{'s} $\mathtt{join\_template}$ (for resolving ambiguous deletions), and the alignment keywords like ``\texttt{key}'' and ``\texttt{best}'' in the \name{Boomerang} language~\citep{Bohannon-Boomerang,Barbosa-matching-lenses} (for specifying keys and matching strategies during alignment) are all constructs which appear in programs designed to look like forward transformations but are meaningful only in the putback direction.
Constructs with similar purposes can also be found in bidirectionalisation approaches, such as \varcitet{Voigtlander-shape-plug-ins}{'s} ``shape bidirectionaliser plug-ins'' (for programming shape changes).
Apart from offering only limited and/or special-purpose customisation of putback behaviour, the fundamental problem with these languages is that their programs contain an ad hoc mixture of forward and backward information, and to properly understand such programs, the only way is to reason in both directions and in terms of the complex underlying semantics.
In other words, it is hard to come up with easy-to-use reasoning principles for these languages, and since reasoning principles reflect and even guide how we program, this indicates that these languages fail to deliver an easy-to-use abstraction.
\BiGUL\ is unique since it offers a successful abstraction in which bidirectional programs become unidirectional and can still be precisely reasoned about, as clearly reflected in the Hoare-style logic.

\varparagraph{The semantics of range triples (\autoref{thm:range-soundness-and-completeness}) is about the |get| direction; consequently, doesn't \autoref{thm:total-forward-consistency} say that we need to reason in both directions anyway, undermining the claim that putback-based reasoning is sufficient?}
Range triples are used only for establishing the domain of |get| --- even without a range triple, a strong enough putback triple alone (i.e., one whose precondition is always true) can already imply that the |get| behaviour is constrained by the consistency relation (\autoref{thm:partial-forward-consistency}).
And, starting from \autoref{lem:range-interpretation}, we have explained how range triples can be understood and derived by thinking in the putback direction, without having to introduce the |get| semantics (except for the precondition of |replace|, which is only a minor exception though); this is particularly evident in the |case| range rule, which is much more awkward to interpret in the |get| direction.
Even if a sceptical reader insisted on thinking about range triples in the |get| direction, it would still be much easier to prove that |get| is contained in the precondition for |put| (as required by \autoref{thm:total-forward-consistency}) than to prove that it is contained in the consistency relation, which is usually much smaller than the precondition for |put|.
The indisputable fact is that the major work is done in derivations of putback triples, making the reasoning putback-based.

%\varparagraph{What reasoning principles were there for bidirectional programming?}
%There are some forms of reasoning principles proposed along with some of the more generically designed bidirectional languages --- for example,  \citet{Foster-lenses} offer systematic rules for proving totality, and \citet{Hofmann-symmetric-lenses} give some equational laws originated from category theory.
%None of them aim to be as strong as our Hoare-style logic, however.
%We might say that the fundamental problem with those reasoning principles is that they are only auxiliary and cannot help the programmer to gain an adequate understanding of program behaviour without breaking the abstraction and reasoning in terms of the semantic definitions of the languages.
%By contrast, our Hoare-style logic completely shields the programmer from the highly detailed semantic definition of \BiGUL\ like the one presented by \citet{Ko-BiGUL}, yet still allows the programmer to precisely understand program behaviour with reasonable effort.

\varparagraph{Where is lens composition?}
In terms of consistency, the behaviour of lens composition is just relational composition; on the other hand, the retentive behaviour of lens composition is rather chaotic and hard to reason about, because its |put| direction is defined in terms of both the |put| and |get| directions of the lenses being composed.
We can formulate a rule like:
\[ \begin{array}{l}
|{-"\phantom{\{\!}"-}(ASSERT (a b' || (some(b, c)) R a c && R' a b && U' b' b c)) ~ {-"\kern2pt"-}l ~ {-"\phantom{\{\!}"-}(ASSERT(COM(a' _ b || R' a' b) CAP T')| \\
|(ASSERTRANGE (a b' || (some(b, c)) R a c && R' a b && U' b' b c)) ~ l ~ (ASSERTRANGE P')| \\
|{-"\phantom{\{\!}"-}(ASSERT (b c || (some(a)) R' a b && R a c)) ~ r ~ (ASSERT U')|
\\ \hline
|{-"\phantom{\{\!}"-}(ASSERT(R CAP (COM(a _ || P' a)))) ~ l . r ~ (ASSERT(a' a c || (some(b, b')) T' a' a b' && U' b' b c ))|
\end{array} \]
and we have actually proved that the rule is sound, but the form of the rule is too complex to be easily usable.
We will need to find a sweet spot and design a composition rule that is perhaps not as general as the above one but can still say enough about the retentive behaviour; most importantly, this rule should give guidance on how composition can be used and reasoned about in practice.
%and only with such a rule can composition be justified as a worthy construct.
It should be noted that while composition is included in other languages like \varcitet{Foster-lenses}{'s} original lenses (and in fact the \Haskell\ port of \BiGUL), the problem with controlling the retentive behaviour of composition has always existed, as discussed by, e.g., \citet[Section~2.2]{Diskin-delta-asymmetric}.

\varparagraph{Are there more examples of verified \BiGUL\ programs?}
In the supplementary \Agda\ code, there is one more program |replaceAll| which replaces all the elements in a source list with a view:
\begin{code}
replaceAll : Eq A => ~ [A] <~ A
replaceAll =  case
              ^  adaptive [] _
              ^  ^  \ _ x -> x :: []
              ^  normal (_ :: []) _ exit (_ :: [])
              ^  ^  rearrS (s :: []) -> s
              ^  ^  ^  replace
              ^  normal _ _ exit (_ :: _ :: _)
              ^  ^  rearrS (s :: ss) -> (s, ss)
              ^  ^  ^  rearrV v -> (v, v)
              ^  ^  ^  ^  replace
              ^  ^  ^  *  replaceAll
\end{code}
for which the following triples are verified:
\begin{code}
(all(n)){-"\hspace{.75em}"-}  {-"\phantom{\{}\!"-}(ASSERT(ss _ | length ss = n)) ~  replaceAll ~
                              {-"\phantom{\{}\!"-}(ASSERT(ss' ss v | ((all(t)) t `elem` ss' => t = v) && (ss /= [] => length ss' = length ss)))

(all(n)){-"\hspace{.75em}"-}  (ASSERTRANGE(ss _ | length ss = n)) ~                 replaceAll ~ (ASSERTRANGE((s' :: ss') | 1 + length ss' = n && (all(t)) t `elem` ss' => s' = t))
\end{code}
This example helps to clarify the misconception that, when programming |put|, the programmer still needs to have a |get| in mind --- rather, what the programmer needs to have in mind is a consistency relation (|COM(ss' v || (all(t)) t `elem` ss' => t = v)| in this case), which may be functional but does not need to be executable.
%whereas |get replaceAll| has additional and non-trivial computational content, which is derived from the |replaceAll| program
The range triple is also interesting as it has a non-trivial output range.

Rather than developing more examples at this stage, we plan to move forward and aim for the verification of practical bidirectional applications.
This will require better mechanised support than the current \Agda\ formalisation, which is exceedingly tedious to work with.
We plan to adapt the Hoare-style logic for automated theorem proving (perhaps in the style of \name{LiquidHaskell}~\citep{Vazou-LiquidHaskell}), so as to verify larger-scale bidirectional programs with reasonable effort.

%\varparagraph{Why isn't the title of this paper ``An Axiomatic Basis for \emph{Putback-Based} Bidirectional Programming''?}
%Within the realm of asymmetric lenses, the get-based approach is fundamentally just about \emph{programming consistency specifications}; only with the putback-based approach can we start talking about \emph{programming to meet functional specifications}, and only in this case does an axiomatic semantics make sense.

%Note that consistency is specified purely relationally in this case.
%This reinforces the statement that it is the consistency relation that we have in mind before programming |put|, rather than the |get| function: for asymmetric lenses, a consistency relation must be functional (in the sense that every source is related to at most one view) but may well not be executable (as in the case of |replaceAll|), whereas a |get| function is executable, and its computational content is non-trivially derived from the |put| program.
%\todo{Discuss asymmetric lenses from \citet[Section~4.1]{Stevens-QVT}'s perspective somewhere before, or move the entire remark to \autoref{sec:discussion}.}
%\begin{proposition}
%\[ |(ASSERT R) ~ b ~ (ASSERT(s' s _ || s' = s))| \quad|=>|\quad |R ~ SUBSETEQ ~ (GRAPH(get b))| \]
%\end{proposition}

%Completeness has not been proved, but we have shown that the logic works for various examples. Relationship with constructive continuity.

%\BiGUL\ is stateful, but only in the ``Reader'' way, in particular using the Reader monad's `|local|' operation to modify the current source and view.
%Our Hoare-style logic can be said to be merely tracking how the current source and view are manipulated by implicit `|local|' operations.

%Towards a syntactic treatment for automation.

\section{Conclusion}
\label{sec:conclusion}

Based on \autoref{lem:dominance}, it has been argued that ``putback'' is the essence of bidirectional programming~\citep{Fischer-essence-of-BX}.
We would like to amend this statement: putback-based \emph{reasoning} is the essence of bidirectional programming.
With the Hoare-style logic for \BiGUL, we have demonstrated how we can understand a \BiGUL\ program's bidirectional behaviour by reasoning exclusively about its putback behaviour, reducing bidirectional programming to unidirectional programming.

Bidirectional programming has been based on a declarative model, in which the programmer writes a consistency specification and relies on the system to produce a well-behaved implementation, whose consistency restoration behaviour can be customised to varying extents but usually in ad hoc and/or awkward ways.
However, it has long been realised that declarative approaches are hardly enough for practical bidirectional applications (see, e.g., \citet[Section~4.1]{Stevens-QVT}).
The bidirectional transformations community currently concentrates on the exploration of more forms of well-behavedness laws (see, e.g., \citet{Cheney-least-surprise}), but we should not be satisfied with only well-behavedness guarantees.
Instead, we should also start aiming to precisely characterise the behaviour of bidirectional programs like what the \BiGUL\ programmer can now do with the Hoare-style logic, and only then can we think about more complex bidirectional applications and the verification of their consistency restoration behaviour.
%treating bidirectional programming as seriously as we treat general-purpose programming.\todo{verification tools}

More broadly, we believe that programming languages should be shipped with reasoning principles --- even domain-specific languages deserve domain-specific reasoning principles, to justify that the languages offer adequate abstractions, and to help the programmer to work effectively and reliably with those abstractions.
In the case of \BiGUL, the Hoare-style logic reflects the somewhat stateful nature of \BiGUL\ programming, and is designed domain-specifically such that the programmer can work out the precise behaviour of \BiGUL\ programs with reasonable effort (rather than breaking the abstraction and working with the messier underlying semantics).
Moreover, the evolution of \BiGUL\ is partly prompted by the development of the Hoare-style logic, whose eventual simplicity justifies \BiGUL's current design.
If, as \citet{Dijkstra-EWD361} argued, programs and their correctness proofs should grow hand in hand, then programming languages and their reasoning principles ought to be developed together as well.
\BiGUL\ and its Hoare-style logic make a nice example of this statement.

%% Acknowledgements
\begin{acks}                            %% acks environment is optional
                                        %% contents suppressed with 'anonymous'
  %% Commands \grantsponsor{<sponsorID>}{<name>}{<url>} and
  %% \grantnum[<url>]{<sponsorID>}{<number>} should be used to
  %% acknowledge financial support and will be used by metadata
  %% extraction tools.
We would like to thank Jeremy Gibbons, Li Liu, and Zirun Zhu for commenting on drafts of this paper, Shin-Cheng Mu for the fruitful discussions during his visit at NII, and Zhixuan Yang for proofreading the manuscript.
We also thank the anonymous reviewers for their valuable comments, and our shepherd James Cheney for checking a nearly final version of this paper.
This work is partially supported by the \grantsponsor{GS501100001691}{Japan Society for the Promotion of Science}{https://doi.org/10.13039/501100001691} (JSPS) Grant-in-Aid for Scientific Research (A)~No.~\grantnum{GS501100001691}{25240009} and (S)~No.~\grantnum{GS501100001691}{17H06099}.
\end{acks}

%% Bibliography
\bibliography{../../../Documents/bib}


%% Appendix
%\appendix
%\section{Appendix}
%
%Text of appendix \ldots

\end{document}

\begin{code}
(ASSERT(_ _))
replaceAll
(ASSERT(ss' ss v | ((all(s')) s' `elem` ss' => s' = v) && (ss /= [] => length ss' = length ss)))
(ASSERTRANGE((s :: ss) | (all(s')) s' `elem` ss => s = s'))
\end{code}

\begin{code}
replaceAll : Eq A => ~ [A] <~ A
replaceAll =
  (ASSERT(ss v | length ss = n))
  (ASSERT(ss v | length ss = n || (n = 0 && length ss = 1)))
  case
    adaptive [] x
      (ASSERT([] v | 0 = n || (n = 0 && 0 = 1)))
      \ _ x -> [x]
      (ASSERT'(reentry)(COM(ss v | length ss = n || (n = 0 && length ss = 1)) [x] x && (COM((_ :: []) _)) [x] x))
      (ASSERT'(postcondition)(all(ss') Post ss' [x] x => Post ss' [] x))
    normal (_ :: []) _ exit (_ :: [])
      (ASSERT((_ :: []) v | 1 = n || (n = 0 && 1 = 1)))
      (ASSERT((_ :: []) v))
      rearrS (s :: []) -> s
        (ASSERT(_ _))
        replace
        (ASSERT(s' _ v | s' = v))
      (ASSERT((s' :: []) (_ :: []) v | s' = v))
    normal _ _ exit (_ :: _ :: _)
      (ASSERT((_ :: _ :: ss) v | 2 + length ss = n || (n = 0 && 2 + length ss = 1)))
      (ASSERT((_ :: _ :: ss) v | 2 + length ss = n))
      rearrS (s :: ss) -> (s, ss)
        (ASSERT((_, _ :: ss) v | 2 + length ss = n))
        rearrV v -> (v, v)
          (ASSERT((_, _ :: ss) (v, w) | v = w && 2 + length ss = n))
          (ASSERT((_, _ :: ss) (v, w) | 2 + length ss = n))
             (ASSERT(_ _))
             replace
             (ASSERT(x _ v | x = v))
          *  (ASSERT((_ :: ss) w | 2 + length ss = n))
             (ASSERT((_ :: ss) w | 1 + length ss = pred n && pred n < n))
             replaceAll
             (ASSERT(ss' ss v | ((all(s')) s' `elem` ss' => s' = v) && (ss /= [] => length ss' = length ss)))
             (ASSERT((y :: ss') (_ :: ss) w | ((all(s')) s' `elem` (y :: ss') => s' = w) && length ss' = length ss))
             (ASSERT((y :: ss') (_ :: ss) w | y = w && ((all(s')) s' `elem` ss' => s' = w) && length ss' = length ss))
          (ASSERT((x, y :: ss') (_, _ :: ss) (v, w) | v = w && x = v && y = w && ((all(s')) s' `elem` ss' => s' = w) && length ss' = length ss))
          (ASSERT((x, y :: ss') (_, _ :: ss) (v, w) | v = w && x = v && y = v && ((all(s')) s' `elem` ss' => s' = v) && length ss' = length ss))
        (ASSERT((x, y :: ss') (_, _ :: ss) v | x = v && y = v && ((all(s')) s' `elem` ss' => s' = v) && length ss' = length ss))
      (ASSERT((x :: y :: ss') (_ :: _ :: ss) v | x = v && y = v && ((all(s')) s' `elem` ss' => s' = v) && length ss' = length ss))
    (ASSERT'(coverage)(True))
    (ASSERT'(disjointness)(True))
  (ASSERT(ss' ss v | ((all(s')) s' `elem` ss' => s' = v) && (ss /= [] => length ss' = length ss)))
\end{code}

\begin{code}
(ASSERTRANGE(ss v | length ss = n))
(ASSERTRANGE(COM([] v | 0 = n) CUP (COM((s::ss) v | 1 + length ss = n && s = v))))
replaceAll
(ASSERTRANGE((s :: ss) | 1 + length ss = n && (all(s')) s' `elem` ss => s = s'))
\end{code}

\begin{code}
(ASSERTRANGE(COM([] v | 0 = n) CUP (COM((s::ss) v | 1 + length ss = n && s = v))))
case
  adaptive [] x
    \ _ x -> [x]
  normal (_ :: []) _ exit (_ :: [])
    (ASSERTRANGE((s::[]) v | 1 = n && s = v))
    rearrS (s :: []) -> s
      (ASSERTRANGE(s v | 1 = n && s = v))
      replace
      (ASSERTRANGE(_ | 1 = n))
    (ASSERTRANGE(s :: [] | 1 = n))
  normal _ _ exit (_ :: _ :: _)
    (ASSERTRANGE((x :: y :: ss) v | 2 + length ss = n && x = v))
    rearrS (s :: ss) -> (s, ss)
      (ASSERTRANGE((x, y :: ss) v | 2 + length ss = n && x = v))
      rearrV v -> (v, v)
        (ASSERTRANGE((x, y :: ss) (v, w) | 2 + length ss = n && x = v && v = w))
        (ASSERTRANGE((x, y :: ss) (v, w) | 2 + length ss = n && x = v && y = w))
           (ASSERTRANGE(x v | x = v))
           replace
           (ASSERTRANGE(_))
        *  (ASSERTRANGE((y :: ss) w | 2 + length ss = n && y = w))
           (ASSERTRANGE((y :: ss) w | 1 + length ss = pred n && y = w))
           replaceAll
           (ASSERTRANGE((s :: ss) | 1 + length ss = pred n && ((all(s')) s' `elem` ss => s = s') && pred n < n))
        (ASSERTRANGE((_, s :: ss) | 1 + length ss = pred n && ((all(s')) s' `elem` ss => s = s') && pred n < n))
        (ASSERTRANGE((x, y :: ss) | 2 + length ss = n && x = y && (all(s')) s' `elem` ss => x = s'))
      (ASSERTRANGE((x, y :: ss) | 2 + length ss = n && x = y && (all(s')) s' `elem` ss => x = s'))
    (ASSERTRANGE((x :: y :: ss) | 2 + length ss = n && x = y && (all(s')) s' `elem` ss => x = s'))
(ASSERTRANGE((s :: ss) | 1 + length ss = n && (all(s')) s' `elem` ss => s = s'))
\end{code}
