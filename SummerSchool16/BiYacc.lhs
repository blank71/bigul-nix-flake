% !TEX root = paper.tex

%include lhs2TeX-macros.lhs

\section{Parsing and reflective printing}

\ignore{
\begin{code}
{-# LANGUAGE TemplateHaskell, TypeFamilies #-}

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

When we mention the \emph{front-end} of a compiler, we usually think of a \emph{parser} that turns concrete syntax, which is designed to be programmer-friendly and provides convenient syntactic sugar, into abstract syntax, which is concise, structured, and easily manipulable by the compiler back-end.
There is another direction, though, in which a \emph{printer} turns abstract syntax back into concrete syntax.
This is useful, for example, for reporting the result of compiler optimizations done on abstract syntax to the programmer, who knows only concrete syntax.
In this case, though, we would want to print the optimized program in a form that is as close to the original program as possible, so the programmer can spot what are changed --- and not changed --- correctly and more easily.
This is where the notion of \emph{reflective printing} comes in: By taking both the original concrete program and the optimized abstract program as input, we can try to retain the look of the original program as much as possible.
Below we will use a simplified arithmetic expression language to explain how reflective printing can be implemented in BiGUL.

\subsection{Well-behavedness}

It is probably obvious that the idea of reflective printing comes from |put| transformations; parsing, then, is the |get| direction.
Before we proceed to implement parsing and reflective printing in BiGUL, a natural question to ask is:
Is well-behavedness meaningful in the context of parsing of reflective printing?
The answer is yes, especially for \ref{eq:PutGet}: An abstract syntax tree (AST) may be thought of as a concise and canonical representation of a concrete program, so it would be strange if a concrete program printed from an AST could not be parsed back to the same AST.
\ref{eq:GetPut}, on the other hand, is in fact not strong enough for our purpose, as it only says that, when an AST is unmodified, printing it reflectively to the original program does not change anything, whereas we would have liked to also say that ``small'' changes to the AST leads to only ``small'' changes to the concrete program.
It is at least a good start to have \ref{eq:GetPut}, though.
We thus conclude that BiGUL is indeed a suitable language for implementing reflective printers and corresponding parsers.

\subsection{Additive expressions}

Here we use a minimal example which is simple and yet can demonstrate what reflective printing is capable of.
Consider the following abstract syntax of arithmetic expressions consisting of integer constant, addition, and subtraction:
\begin{code}
data Arith  =  Num Int
            |  Add  Arith Arith
            |  Sub  Arith Arith
  deriving Show
\end{code}
This is a nice representation for the compiler, but we cannot expect the programmer to write something like ``|Sub (Num 1) (Add (Num 2) (Num 3))|'', and should provide a concrete syntax so they can write ``$1 - (2+3)$''.
Such a concrete syntax is usually defined in terms of a BNF grammar:
\begin{spec}
Exp     ->  Exp '+' Factor
        |   Exp '-' Factor
        |   Factor

Factor  ->  Int
        |   '-' Factor
        |   '(' Exp ')'
\end{spec}
The two-level structure of |Exp| and |Factor| ensures that plus and minus associate to the left by default; to change association, we should use parentheses.
And, to spice up the problem a little, we allow minus to be used also as a negative sign, as specified by the second production rule for |Factor|.
BiGUL deals with structured data only, so we should represent a string generated using this grammar as a concrete syntax tree of the following type:
\begin{code}
data Exp  =  Plus   Exp Factor
          |  Minus  Exp Factor
          |  EF Factor
          |  ENull

data Factor  =  Lit  Int
             |  Neg  Factor
             |  Paren Exp
             |  FNull
\end{code}%
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
parseExp :: String -> Either ParseError Exp

unsafeParseExp    ::  String -> Exp
unsafeParseExp s  =   let (Right e) = parseExp s in e
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

parseExp :: String -> Either ParseError Exp
parseExp = tokeniseAndParse expTokeniser expParser

unsafeParseExp    ::  String -> Exp
unsafeParseExp s  =   let (Right e) = parseExp s in e
\end{code}
}%
The rest of the job is then write a BiGUL program between |Exp| and |Arith|.

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
$(update  [p| Plus l r |] [p| Add l r |]
          [d| l = pExpArith; r = pFactorArith |])
\end{spec}
Following the same line of thought, we can fill in other branches to relate all abstract constructors with concrete production rules:
\begin{spec}
pExpArith  ::  BiGUL Exp Arith
pExpArith  =   Case
  [ $(normalSV [p| Plus _ _ |] [p| Add _ _ |] [p| Plus _ _ |])
    ==> $(update  [p| Plus l r |] [p| Add l r |]
                  [d| l = pExpArith; r = pFactorArith |])
  , $(normalSV [p| Minus _ _ |] [p| Sub _ _ |] [p| Minus _ _ |])
    ==> $(update  [p| Minus l r |] [p| Sub l r |]
                  [d| l = pExpArith; r = pFactorArith |])
  , $(normalSV [p| EF _ |] [p| _ |] [p| EF _ |])
    ==> $(update  [p| EF t |] [p| t |]
                  [d| t = pFactorArith |])
  ]

pFactorArith  ::  BiGUL Factor Arith
pFactorArith  =   Case
  [ $(normalSV [p| Lit _ |] [p| Num _ |] [p| Lit _ |])
    ==> $(update [p| Lit i |] [p| Num i |] [d| i = Replace |])
  , $(normalSV [p| Neg _ |] [p| Sub (Num 0) _ |] [p| Neg _ |])
    ==> $(update [p| Neg t |] [p| Sub (Num 0) t |] [d| t = pFactorArith |])
  , $(normalSV [p| Paren _ |] [p| _ |] [p| Paren _ |])
    ==> $(update [p| Paren t |] [p| t |] [d| t = pExpArith |])
  ]
\end{spec}

This covers only ``normal'' cases though, namely when the source and view are ``the same'' except for parentheses and literals.
What about the cases when the source and view have mismatched shapes?
For these cases, we need adaptation.
Corresponding to each branch we have already written, we add an adaptive branch which looks at the shape of the view only, throws away a mismatched source, and creates an incomplete one whose shape matches that of the view; the source will be complete created through recursive processing.
For example, corresponding to the plus/addition branch, we write:
\begin{spec}
S(adaptiveSV (P(_)) (P(Add _ _)))
  ==> \ _ _ -> Plus ENull FNull
\end{spec}
The full programs are:
\begin{code}
pExpArith  ::  BiGUL Exp Arith
pExpArith  =   Case
  [ $(normalSV [p| Plus _ _ |] [p| Add _ _ |] [p| Plus _ _ |])
    ==> $(update [p| Plus l r |] [p| Add l r |]
                 [d| l = pExpArith; r = pFactorArith |])
  , $(normalSV [p| Minus _ _ |] [p| Sub _ _ |] [p| Minus _ _ |])
    ==> $(update [p| Minus l r |] [p| Sub l r |]
                 [d| l = pExpArith; r = pFactorArith |])
  , $(normalSV [p| EF _ |] [p| _ |] [p| EF _ |])
    ==> $(update [p| EF t |] [p| t |]
                 [d| t = pFactorArith |])
  , $(adaptiveSV [p| _ |] [p| Add _ _ |])
    ==> \ _ _ -> Plus ENull FNull
  , $(adaptiveSV [p| _ |] [p| Sub _ _ |])
    ==> \ _ _ -> Minus ENull FNull
  , $(adaptiveSV [p| _ |] [p| _ |])
    ==> \ _ _ -> EF FNull
  ]

pFactorArith  ::  BiGUL Factor Arith
pFactorArith  =   Case
  [ $(normalSV [p| Lit _ |] [p| Num _ |] [p| Lit _ |])
    ==> $(update [p| Lit i |] [p| Num i |] [d| i = Replace |])
  , $(normalSV [p| Neg _ |] [p| Sub (Num 0) _ |] [p| Neg _ |])
    ==> $(update [p| Neg t |] [p| Sub (Num 0) t |] [d| t = pFactorArith |])
  , $(normalSV [p| Paren _ |] [p| _ |] [p| Paren _ |])
    ==> $(update [p| Paren t |] [p| t |] [d| t = pExpArith |])
  , $(adaptiveSV [p| _ |] [p| Num _ |])
    ==> \ _ _ -> Lit 0
  , $(adaptiveSV [p| _ |] [p| Sub (Num 0) _ |])
    ==> \ _ _ -> Neg FNull
  , $(adaptiveSV [p| _ |] [p| _ |])
    ==> \ _ _ -> Paren ENull
  ]
\end{code}

\subsection{Reflecting optimizations and evaluation sequences}

The BiGUL programs, being bidirectional, can be executed in the |put| direction as a reflective printer, or in the |get| direction as a parser.
Let us look at parsing first. For example:
\begin{verbatim}
*Main> get pExpArith (unsafeParseExp "(-(3+4))")
Just (Sub (Num 0) (Add (Num 3) (Num 4)))
\end{verbatim}
Note that a unary minus is considered as syntactic sugar, and is desugared into a subtraction whose left operand is zero.
Also note that parentheses are turned into correct structure of the abstract syntax tree, and nothing more --- excessive parentheses are cleanly discarded.

For reflective printing, as we mentioned, one application is reporting what compiler optimizations do.
We can replace the sub-expression $3+4$ with its value~$1$, for example, and the reflective printer will be able to retain the excessive parentheses:
\begin{verbatim}
*Main> put pExpArith (unsafeParseExp "(-(3+4))")
                     (Sub (Num 0) (Num 7))
Just (-(7))
\end{verbatim}
Notice also that the unary minus is preserved.
If the original concrete expression uses a binary minus instead, it will be preserved as well:
\begin{verbatim}
*Main> put pExpArith (unsafeParseExp "(0-(3+4))")
                     (Sub (Num 0) (Num 7))
Just (0-(7))
\end{verbatim}

More generally, the steps in an evaluation sequence of an abstract syntax tree can all be reflected to concrete syntax.
For example, starting from:
\begin{verbatim}
*Main> get pExpArith (unsafeParseExp "1+(2+3)")
Just (Add (Num 1) (Add (Num 2) (Num 3)))
\end{verbatim}
it takes two steps to evaluate this expression:
\begin{verbatim}
*Main> put pExpArith (unsafeParseExp "1+(2+3)")
                     (Add (Num 1) (Num 5))
Just 1+(5)
*Main> put pExpArith (unsafeParseExp "1+(5)") (Num 6)
Just 6
\end{verbatim}
This means that if we have an evaluator on the abstract syntax, we will automatically get an evaluator on the concrete syntax!

A reflective printer can also be used as an ordinary printer by setting the original source to an empty one.
For example:
\begin{verbatim}
*Main> put pExpArith ENull (Sub (Num 0) (Add (Num 1) (Num 1)))
Just 0-(1+1)
\end{verbatim}
You have probably noticed that the subtraction is reflected as a binary minus instead of a unary one, despite that the left operand is zero.
This behavior is easily customizable:
By adding an adaptive branch before the one dealing generically with |Sub| in |pExpArith|:
\begin{spec}
$(adaptiveSV [p| _ |] [p| Sub (Num 0) _ |])
  ==> \ _ _ -> EF FNull
\end{spec}
the above abstract syntax tree can be printed as:
\begin{verbatim}
*Main> put pExpArith ENull (Sub (Num 0) (Add (Num 1) (Num 1)))
Just -(1+1)
\end{verbatim}

\subsection{A domain-codeific language}

As a final remark, the above programs may look long, but at the core of them are merely the correspondences between concrete production rules and abstract constructors.
We can design a domain-specific language (DSL) that expresses such correspondences concisely, and then expand programs in this DSL into BiGUL.
In fact, we have already done so, and the DSL is called \emph{BiYacc}.
For example, all the programs we have written can be generated from the following eight-line BiYacc program:
\begin{verbatim}
  Arith +> Exp
  Add l r +> (l +> Exp) '+' (r +> Factor);
  Sub l r +> (l +> Exp) '-' (r +> Factor);
  f       +> (f +> Factor);

  Arith +> Factor
  Num n         +> (n +> Int);
  Sub (Num 0) r +> '-' (r +> Factor);
  f             +> '(' (f +> Exp) ')';
\end{verbatim}
See our draft paper\footnote{\url{http://www.prg.nii.ac.jp/members/zhu/papers/sle2016_draft.pdf}} for more interesting experiments about reflective printing, done on a more realistic imperative language.
