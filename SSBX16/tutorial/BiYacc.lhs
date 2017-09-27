% !TEX root = tutorial.tex

%include lhs2TeX-macros.lhs

\section{Parsing and reflective printing}
\label{sec:BiYacc}

\ignore{
\begin{code}
{-# LANGUAGE TemplateHaskell, TypeFamilies #-}

module BiYacc where

import Generics.BiGUL
import Generics.BiGUL.TH
import Generics.BiGUL.Lib
import Generics.BiGUL.Interpreter

import GHC.Generics
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Pos
\end{code}
}

When we mention the \emph{front-end} of a compiler, we usually think of a \emph{parser} that turns \emph{concrete syntax}, which is designed to be programmer-friendly and provides convenient syntactic sugar, into \emph{abstract syntax}, which is concise, structured, and easily manipulable by the compiler back-end.
There is another direction, though, in which a \emph{printer} turns abstract syntax back into concrete syntax.
This is useful, for example, for reporting the result of compiler optimizations done on abstract syntax to the programmer, who knows only concrete syntax.
In this case, though, we would want to print the optimized program in a form that is as close to the original program as possible, so the programmer can spot what has changed --- and not changed --- correctly and more easily.
This is where the notion of \emph{reflective printing} comes in: By taking both the original concrete program and the optimized abstract program as input, we can try to retain the look of the original program as much as possible.
Below we will use a simplified arithmetic expression language to explain how reflective printing can be implemented in BiGUL.

\subsection{Well-behavedness}

It is probably obvious that the idea of reflective printing comes from |put| transformations; parsing, then, is the |get| direction.
Before we proceed to implement parsing and reflective printing in BiGUL, a natural question to ask is:
is well-behavedness meaningful in the context of parsing of reflective printing?
The answer is yes, especially for \ref{eq:PutGet}: An abstract syntax tree (AST) may be thought of as a concise and canonical representation of a concrete program, so it would be strange if a concrete program printed from an AST could not be parsed back to the same AST.
\ref{eq:GetPut}, on the other hand, is in fact not strong enough for our purpose, as it only says that, when an AST is unmodified, printing it reflectively to the original program does not change anything, whereas we would have liked to also say that ``small'' changes to the AST lead to only ``small'' changes to the concrete program.
That is, we would like reflective printing to conform to some sort of least-change principle, a topic which is still unsettled and actively investigated by the BX community.
It is at least a good start to have \ref{eq:GetPut}, though.
We thus conclude that BiGUL is indeed a suitable language for implementing reflective printers and corresponding parsers.

\subsection{Additive expressions}

Here we use a minimal example which is simple and yet can demonstrate what reflective printing is capable of.
Consider the following abstract syntax of arithmetic expressions consisting of integer constants, addition, and subtraction:
\begin{code}
data Arith  =  Num Int
            |  Add  Arith Arith
            |  Sub  Arith Arith
            deriving Show
\end{code}
This is a nice representation for the compiler, but we cannot expect the programmer to write something like ``|Sub (Num 1) (Add (Num 2) (Num 3))|'', and should provide a concrete syntax so that they can write ``$1 - (2+3)$''.
Such a concrete syntax is usually defined in terms of a BNF grammar:
\begin{spec}
Exp     ->  Exp {-"\texttt{\textquotesingle+\textquotesingle}\;"-} Factor
        |   Exp {-"\texttt{\textquotesingle-\textquotesingle}\;"-} Factor
        |   Factor

Factor  ->  Int
        |   {-"\texttt{\textquotesingle-\textquotesingle}\;"-} Factor
        |   {-"\texttt{\textquotesingle(\textquotesingle}\;"-} Exp {-"\;\texttt{\textquotesingle)\textquotesingle}"-}
\end{spec}
The two-level structure of |Exp| and |Factor| ensures that plus and minus associate to the left by default; to change association, we should use parentheses.
And, to spice up the problem a little, we allow minus to be used also as a negative sign, as specified by the second production rule for |Factor|.
BiGUL deals with structured data only, so we should represent a string generated using this grammar as a concrete syntax tree of the following type:
\begin{code}
data Exp  =   Plus Exp Factor
          |   Minus Exp Factor
          |   EF Factor
          |   ENull

data Factor  =  Lit Int
             |  Neg Factor
             |  Paren Exp
             |  FNull
\end{code}%
Again, we need to provide one |deriveBiGULGeneric| statement for each of the above datatypes to allow BiGUL to operate on them:
\begin{align*}
& |deriveBiGULGeneric|\;\texttt{\char13\char13}|Arith| \\
& |deriveBiGULGeneric|\;\texttt{\char13\char13}|Exp| \\
& |deriveBiGULGeneric|\;\texttt{\char13\char13}|Factor|
\end{align*}
\ignore{%
\begin{code}
deriveBiGULGeneric ''Arith
deriveBiGULGeneric ''Exp
deriveBiGULGeneric ''Factor
\end{code}
}%
Apart from the |Null| constructors, which are inserted to represent incomplete trees that can occur during reflective printing, these two datatypes are in direct correspondence with the grammar, so it is easy to recover the string from a concrete syntax tree:
\begin{code}
instance Show Exp where
  show (  Plus   e  f)  =  show e ++ "+" ++ show f
  show (  Minus  e  f)  =  show e ++ "-" ++ show f
  show (  EF        f)  =  show f
  show    ENull         =  "."

instance Show Factor where
  show (  Lit    n   )   =  show n
  show (  Neg    f   )   =  "-" ++ show f
  show (  Paren  e   )   =  "(" ++ show e ++ ")"
  show    FNull          =  "."
\end{code}
Conversely, using modern parser technologies like Haskell's \texttt{parsec} parser combinator library, we can easily implement a ``concrete parser'' that turns a string into a concrete syntax tree:
\begin{spec}
parseExp :: String -> Exp
\end{spec}%
\ignore{%
\begin{code}
(>|>=) :: Monad m => m a -> (a -> m b) -> m a
(>|>=) mx f = mx >>= \x -> f x >> return x

(>|>) :: Monad m => m a -> m b -> m a
(>|>) mx my = mx >|>= const my

alternatives :: [GenParser tok st a] -> GenParser tok st a
alternatives = foldr1 ((<|>) . try)

data ExpToken = LitTok Int | PlusTok | MinusTok | LParen | RParen deriving (Eq, Show)

expTokeniser :: Parser ExpToken
expTokeniser =
  alternatives
    [liftM (LitTok . read) (many1 digit),
     char '+' >> return PlusTok,
     char '-' >> return MinusTok,
     char '(' >> return LParen,
     char ')' >> return RParen]

lit :: GenParser ExpToken () Int
lit = token show (const (initialPos "")) (\t -> case t of { LitTok n -> Just n; _ -> Nothing })

expToken :: ExpToken -> GenParser ExpToken () ExpToken
expToken tok = token show (const (initialPos "")) (\t -> if t == tok then Just tok else Nothing)

expParser :: GenParser ExpToken () Exp
expParser =
  liftM (either EF id)
    (chainl1
       (liftM Left factorParser)
       (liftM (\op -> f (if op == PlusTok then Plus else Minus))
              (alternatives [expToken PlusTok, expToken MinusTok])))
  where
    f :: (Exp -> Factor -> Exp) -> Either Factor Exp -> Either Factor Exp -> Either Factor Exp
    f con (Left  lhsFactor) (Left rhsFactor) = Right (con (EF lhsFactor) rhsFactor)
    f con (Right lhsExp   ) (Left rhsFactor) = Right (con lhsExp rhsFactor)
    f con _                 (Right _       ) = error "expParser: the impossible happened"

factorParser :: GenParser ExpToken () Factor
factorParser =
  alternatives
    [liftM Lit lit,
     expToken MinusTok >> liftM Neg factorParser,
     expToken LParen >> (liftM Paren expParser >|> expToken RParen)]

tokeniseAndParse :: Parser tok -> GenParser tok () a -> String -> Either ParseError a
tokeniseAndParse tokeniser parser = (parse parser "" =<<) . parse (many tokeniser >|> eof) ""

safeParseExp :: String -> Either ParseError Exp
safeParseExp = tokeniseAndParse expTokeniser expParser

parseExp    ::  String -> Exp
parseExp s  =   let (Right e) = safeParseExp s in e
\end{code}
}%
The rest of the job is then to write a BiGUL program between |Exp| and |Arith|.

\subsection{Reflective printing in BiGUL}

The program is basically a case analysis: For example, when the concrete side is a plus and the abstract side is an addition, they match, and we can go into their sub-trees recursively.
For the concrete side, the right sub-tree is of type |Factor| instead of |Exp|, so in fact we will write two (mutually recursive) programs:
\begin{spec}
pExpArith     ::  BiGUL Exp Arith
pExpArith     =   Case undefined

pFactorArith  ::  BiGUL Factor Arith
pFactorArith  =   Case undefined
\end{spec}
The branch for plus and addition can then be written as:
\begin{spec}
$(update  (P( Plus l r )) (P( Add l r )) (D( l = pExpArith; r = pFactorArith )))
\end{spec}
Following the same line of thought, we can fill in other branches to relate all abstract constructors with concrete production rules:
\begin{spec}
pExpArith  ::  BiGUL Exp Arith
pExpArith  =   Case
  [ $(normalSV (P( Plus _ _ )) (P( Add _ _ )) (P( Plus _ _ )))
    ==> $(update  (P( Plus l r )) (P( Add l r ))
                  (D( l = pExpArith; r = pFactorArith )))
  , $(normalSV (P( Minus _ _ )) (P( Sub _ _ )) (P( Minus _ _ )))
    ==> $(update  (P( Minus l r )) (P( Sub l r ))
                  (D( l = pExpArith; r = pFactorArith )))
  , $(normalSV (P( EF _ )) (P( _ )) (P( EF _ )))
    ==> $(update  (P( EF t )) (P( t ))
                  (D( t = pFactorArith )))
  ]

pFactorArith  ::   BiGUL Factor Arith
pFactorArith  =    Case
  [ $(normalSV (P( Lit _ )) (P( Num _ )) (P( Lit _ )))
    ==> $(update (P( Lit i )) (P( Num i )) (D( i = Replace )))
  , $(normalSV (P( Neg _ )) (P( Sub (Num 0) _ )) (P( Neg _ )))
    ==> $(update (P( Neg t )) (P( Sub (Num 0) t )) (D( t = pFactorArith )))
  , $(normalSV (P( Paren _ )) (P( _ )) (P( Paren _ )))
    ==> $(update (P( Paren t )) (P( t )) (D( t = pExpArith )))
  ]
\end{spec}

This covers only ``normal'' cases though, namely when the source and view are ``the same'' except for parentheses and literals.
What about the cases where the source and view have mismatched shapes?
For these cases, we need adaptation.
Corresponding to each branch we have already written, we add an adaptive branch which looks at the shape of the view only, throws away a mismatched source, and creates an incomplete one whose shape matches that of the view; the source will be completely created through recursive processing.
For example, corresponding to the plus/addition branch, we write:
\begin{spec}
$(adaptiveSV (P( _ )) (P( Add _ _ )))
  ==> \ _ _ -> Plus ENull FNull
\end{spec}
The full programs are:
\begin{code}
pExpArith  ::  BiGUL Exp Arith
pExpArith  =   Case
  [ $(normalSV (P( Plus _ _ )) (P( Add _ _ )) (P( Plus _ _ )))
    ==> $(update  (P( Plus l r )) (P( Add l r ))
                  (D( l = pExpArith; r = pFactorArith )))
  , $(normalSV (P( Minus _ _ )) (P( Sub _ _ )) (P( Minus _ _ )))
    ==> $(update  (P( Minus l r )) (P( Sub l r ))
                  (D( l = pExpArith; r = pFactorArith )))
  , $(normalSV (P( EF _ )) (P( _ )) (P( EF _ )))
    ==> $(update  (P( EF t )) (P( t ))
                  (D( t = pFactorArith )))
  , $(adaptiveSV (P( _ )) (P( Add _ _ )))
    ==> \ _ _ -> Plus ENull FNull
  , $(adaptiveSV (P( _ )) (P( Sub _ _ )))
    ==> \ _ _ -> Minus ENull FNull
  , $(adaptiveSV (P( _ )) (P( _ )))
    ==> \ _ _ -> EF FNull
  ]

pFactorArith  ::   BiGUL Factor Arith
pFactorArith  =    Case
  [ $(normalSV (P( Lit _ )) (P( Num _ )) (P( Lit _ )))
    ==> $(update (P( Lit i )) (P( Num i )) (D( i = Replace )))
  , $(normalSV (P( Neg _ )) (P( Sub (Num 0) _ )) (P( Neg _ )))
    ==> $(update (P( Neg t )) (P( Sub (Num 0) t )) (D( t = pFactorArith )))
  , $(normalSV (P( Paren _ )) (P( _ )) (P( Paren _ )))
    ==> $(update (P( Paren t )) (P( t )) (D( t = pExpArith )))
  , $(adaptiveSV (P( _ )) (P( Num _ )))
    ==> \ _ _ -> Lit 0
  , $(adaptiveSV (P( _ )) (P( Sub (Num 0) _ )))
    ==> \ _ _ -> Neg FNull
  , $(adaptiveSV (P( _ )) (P( _ )))
    ==> \ _ _ -> Paren ENull
  ]
\end{code}

\subsection{Reflecting optimizations and evaluation sequences}

The BiGUL programs, being bidirectional, can be executed in the |put| direction as a reflective printer, or in the |get| direction as a parser.
Let us look at parsing first. For example:
\begin{lstlisting}
*BiYacc> get pExpArith (parseExp "(-(3+0))")
\eval*{get pExpArith (parseExp "(-(3+0))")}
\end{lstlisting}
Note that a unary minus is regarded as syntactic sugar, and is desugared into a subtraction whose left operand is zero.
Also note that parentheses are turned into correct structure of the abstract syntax tree, and nothing more --- excessive parentheses are cleanly discarded.

For reflective printing, as we mentioned, one application is reporting what compiler optimizations do.
We can optimize the sub-expression $3+0$ by getting rid of the superfluous ${}+0$, for example, and the reflective printer will be able to retain the excessive parentheses:
\begin{lstlisting}
*BiYacc> put pExpArith (parseExp "(-(3+0))") (Sub (Num 0) (Num 3))
\eval*{put pExpArith (parseExp "(-(3+0))") (Sub (Num 0) (Num 3))}
\end{lstlisting}
Notice also that the unary minus is preserved.
If the original concrete expression uses a binary minus instead, it will be preserved as well:
\begin{lstlisting}
*BiYacc> put pExpArith (parseExp "(0-(3+0))") (Sub (Num 0) (Num 3))
\eval*{put pExpArith (parseExp "(0-(3+0))") (Sub (Num 0) (Num 3))}
\end{lstlisting}

In the above example, the pair of parentheses around~$3$ is also preserved.
This is more a coincidence, though --- if we change |Sub| to |Add|, for example, the pair of parentheses will not be preserved:
\begin{lstlisting}
*BiYacc> put pExpArith (parseExp "(0-(3+0))") (Add (Num 0) (Num 3))
\eval*{put pExpArith (parseExp "(0-(3+0))") (Add (Num 0) (Num 3))}
\end{lstlisting}
This behavior is indeed what we described with our BiGUL program: the concrete binary minus does not match the abstract |Add|, so the whole concrete expression \verb"0-(3+0)" inside the outermost pair of parentheses is discarded, and a new concrete expression \verb"0+3" is generated by adaptation.
This behavior does not give us ``least change'', however: the pair of parentheses around~$3$ could have been kept.
This is one example showing that, while \ref{eq:GetPut} (no view change implies no source change) is guaranteed by BiGUL, least-change behavior (small view change implies small source change) is another matter completely, and requires extra care and effort to achieve.

Another thing we can do is reflecting the steps in an evaluation sequence of an abstract syntax tree to concrete syntax.
For example, starting from:
\begin{lstlisting}
*BiYacc> get pExpArith (parseExp "1+(2+3)")
\eval*{get pExpArith (parseExp "1+(2+3)")}
\end{lstlisting}
it takes two steps to evaluate this expression:
\begin{lstlisting}
*BiYacc> put pExpArith (parseExp "1+(2+3)") (Add (Num 1) (Num 5))
\eval*{put pExpArith (parseExp "1+(2+3)") (Add (Num 1) (Num 5))}
*BiYacc> put pExpArith (parseExp "1+(5)") (Num 6)
\eval*{put pExpArith (parseExp "1+(5)") (Num 6)}
\end{lstlisting}
This means that if we have an evaluator on the abstract syntax, we will automatically get an evaluator on the concrete syntax!

A reflective printer can also be used as an ordinary printer by setting the original source to an empty one.
For example:
\begin{lstlisting}
*BiYacc> put pExpArith ENull (Sub (Num 0) (Add (Num 1) (Num 1)))
\eval*{put pExpArith ENull (Sub (Num 0) (Add (Num 1) (Num 1)))}
\end{lstlisting}
Note that the subtraction is reflected as a binary minus instead of a unary one, despite that the left operand is zero.
This behavior is easily customizable:
By adding an adaptive branch before the one dealing generically with |Sub| in |pExpArith|:
\begin{spec}
$(adaptiveSV (P( _ )) (P( Sub (Num 0) _ )))
  ==> \ _ _ -> EF FNull
\end{spec}
the above abstract syntax tree can be printed as:
\begin{lstlisting}
*BiYacc> put pExpArith ENull (Sub (Num 0) (Add (Num 1) (Num 1)))
\eval*{put pExpArith ENull (Sub (Num 0) (Add (Num 1) (Num 1)))}
\end{lstlisting}

\subsection{A domain-specific language}

As a final remark, the above programs may look long, but at the core of them are merely the correspondences between concrete production rules and abstract constructors.
We can design a domain-specific language (DSL) that expresses such correspondences concisely, and then expand programs in this DSL into BiGUL.
In fact, we have already done so, and the DSL is called \emph{BiYacc}.
For example, all the programs we have written can be generated from the following eight-line BiYacc program:
\begin{lstlisting}
  Arith +> Exp
  Add l r +> (l +> Exp) '+' (r +> Factor);
  Sub l r +> (l +> Exp) '-' (r +> Factor);
  f       +> (f +> Factor);

  Arith +> Factor
  Num n         +> (n +> Int);
  Sub (Num 0) r +> '-' (r +> Factor);
  f             +> '(' (f +> Exp) ')';
\end{lstlisting}
See our SLE 2016 paper~\cite{Zhu-BiYacc} for more interesting experiments about reflective printing, done on a more realistic imperative language.
