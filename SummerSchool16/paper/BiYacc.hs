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


--------
-- Abstract syntax trees

data Arith = Num Int
           | Add Arith Arith
           | Sub Arith Arith
           deriving Show

deriveBiGULGeneric ''Arith


--------
-- Concrete syntax trees

{-

Exp    -> Exp '+' Factor
       |  Exp '-' Factor
       |  Factor

Factor -> Int
       |  '-' Factor
       | '(' Exp ')'

-}

data Exp = Plus Exp Factor
         | Minus Exp Factor
         | EF Factor
         | ENull

data Factor = Lit Int
            | Neg Factor
            | Paren Exp
            | FNull

deriveBiGULGeneric ''Exp
deriveBiGULGeneric ''Factor

-- we identify well-formed strings and CSTs

instance Show Exp where
  show (Plus  e f) = show e ++ "+" ++ show f
  show (Minus e f) = show e ++ "-" ++ show f
  show (EF      f) = show f
  show  ENull      = "."

instance Show Factor where
  show (Lit   n) = show n
  show (Neg   f) = "-" ++ show f
  show (Paren e) = "(" ++ show e ++ ")"
  show  FNull    = "."

-- show           :: Exp -> String
-- unsafeParseExp :: String -> Exp

_ = show (Plus (EF (Lit 1)) (Lit 1))
_ = unsafeParseExp "1+1"


--------
-- Reflective printer

pExpArith :: BiGUL Exp Arith
pExpArith = Case
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
    ==> \_ _ -> Plus ENull FNull
  , $(adaptiveSV [p| _ |] [p| Sub (Num 0) _ |])
    ==> \_ _ -> EF FNull
  , $(adaptiveSV [p| _ |] [p| Sub _ _ |])
    ==> \_ _ -> Minus ENull FNull
  , $(adaptiveSV [p| _ |] [p| _ |])
    ==> \_ _ -> EF FNull
  ]

pFactorArith :: BiGUL Factor Arith
pFactorArith = Case
  [ $(normalSV [p| Lit _ |] [p| Num _ |] [p| Lit _ |])
    ==> $(update [p| Lit i |] [p| Num i |] [d| i = Replace |])
  , $(normalSV [p| Neg _ |] [p| Sub (Num 0) _ |] [p| Neg _ |])
    ==> $(update [p| Neg t |] [p| Sub (Num 0) t |] [d| t = pFactorArith |])
  , $(normalSV [p| Paren _ |] [p| _ |] [p| Paren _ |])
    ==> $(update [p| Paren t |] [p| t |] [d| t = pExpArith |])
  , $(adaptiveSV [p| _ |] [p| Num _ |])
    ==> \_ _ -> Lit 0
  , $(adaptiveSV [p| _ |] [p| Sub (Num 0) _ |])
    ==> \_ _ -> Neg FNull
  , $(adaptiveSV [p| _ |] [p| _ |])
    ==> \_ _ -> Paren ENull
  ]


--------
-- Test cases (which work well)

-- get works fine
_ = get pExpArith (unsafeParseExp "(-(3+4))")

-- compiler optimisation: replacing 3+4 with 7
_ = put pExpArith (unsafeParseExp "(-(3+4))") (Sub (Num 0) (Num 7))

-- the choice of a unary minus or (in this case) a binary minus is preserved
_ = put pExpArith (unsafeParseExp "(0-(3+4))") (Sub (Num 0) (Num 7))

-- Pombrio and Krishnamurthi’s “resugaring”:
-- reflecting an abstract evaluation sequence to a concrete evaluation sequence
_ = get pExpArith (unsafeParseExp "1+(2+3)")
_ = put pExpArith (unsafeParseExp "1+(2+3)") (Add (Num 1) (Num 5))
_ = put pExpArith (unsafeParseExp "1+(5)") (Num 6)

-- reflective printing subsumes ordinary printing (whose behaviour is customisable)
_ = put pExpArith ENull (Sub (Num 0) (Add (Num 1) (Num 1)))


--------
-- Concrete parser

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

unsafeParseExp :: String -> Exp
unsafeParseExp s = let (Right e) = parseExp s in e
