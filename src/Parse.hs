{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
{-|
Module      : Parse
Description : Define un parser de términos FD40 a términos fully named.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Parse (tm, Parse.parse, decl, runP, P, program, declOrTm) where

import Prelude hiding ( const )
import Lang hiding (getPos)
import Common
import Text.Parsec hiding (runP,parse)
--import Data.Char ( isNumber, ord )
import qualified Text.Parsec.Token as Tok
import Text.ParserCombinators.Parsec.Language --( GenLanguageDef(..), emptyDef )
import qualified Text.Parsec.Expr as Ex
import Text.Parsec.Expr (Operator, Assoc)
import Control.Monad.Identity (Identity)

type P = Parsec String ()

-----------------------
-- Lexer
-----------------------
-- | Analizador de Tokens
lexer :: Tok.TokenParser u
lexer = Tok.makeTokenParser langDef

langDef :: LanguageDef u
langDef = emptyDef {
         commentLine    = "#",
         reservedNames = ["let", "rec","fun", "fix", "then", "else","in",
                           "ifz", "print","Nat","type"],
         reservedOpNames = ["->",":","=","+","-"]
        }

whiteSpace :: P ()
whiteSpace = Tok.whiteSpace lexer

natural :: P Integer 
natural = Tok.natural lexer

stringLiteral :: P String
stringLiteral = Tok.stringLiteral lexer

parens :: P a -> P a
parens = Tok.parens lexer

identifier :: P String
identifier = Tok.identifier lexer

reserved :: String -> P ()
reserved = Tok.reserved lexer

reservedOp :: String -> P ()
reservedOp = Tok.reservedOp lexer

tyIdentifier :: P String
tyIdentifier = Tok.lexeme lexer $ do
  c  <- upper
  cs <- many (identLetter langDef)
  return (c:cs)

-----------------------
-- Parsers
-----------------------

num :: P Int
num = fromInteger <$> natural

var :: P Name
var = identifier

getPos :: P Pos
getPos = do pos <- getPosition
            return $ Pos (sourceLine pos) (sourceColumn pos)

tyatom :: P Ty
tyatom = (reserved "Nat" >> return NatTy)
         <|> parens typeP

typeP :: P Ty
typeP = try (do 
          x <- tyatom
          reservedOp "->"
          y <- typeP
          return (FunTy x y))
      <|> tyatom
          
const :: P Const
const = CNat <$> num

printOp :: P STerm
printOp = do
  i <- getPos
  reserved "print"
  str <- option "" stringLiteral
  a <- atom
  return (SPrint i str a)

binary :: String -> BinaryOp -> Assoc -> Operator String () Identity STerm
binary s f = Ex.Infix (reservedOp s >> return (SBinaryOp NoPos f))

table :: [[Operator String () Identity STerm]]
table = [[binary "+" Add Ex.AssocLeft,
          binary "-" Sub Ex.AssocLeft]]

expr :: P STerm
expr = Ex.buildExpressionParser table tm

atom :: P STerm
atom =     (flip SConst <$> const <*> getPos)
       <|> flip SV <$> var <*> getPos
       <|> parens expr
       <|> printOp

-- parsea un par (variable : tipo)
binding :: P (Name, Ty)
binding = do v <- var
             reservedOp ":"
             ty <- typeP
             return (v, ty)

parensBinding :: P (Name, Ty)
parensBinding = parens binding

binders :: P [(Name, Ty)]
binders = many parensBinding

lam :: P STerm
lam = do i <- getPos
         reserved "fun"
         vars <- binders
        --  (v,ty) <- parens binding
         reservedOp "->"
         t <- expr
         return (SLam i vars t)

-- Nota el parser app también parsea un solo atom.
app :: P STerm
app = do i <- getPos
         f <- atom
         args <- many atom
         return (foldl (SApp i) f args)

ifz :: P STerm
ifz = do i <- getPos
         reserved "ifz"
         c <- expr
         reserved "then"
         t <- expr
         reserved "else"
         e <- expr
         return (SIfZ i c t e)

fix :: P STerm
fix = do i <- getPos
         reserved "fix"
         (f, fty) <- parens binding
         vars <- binders
         reservedOp "->"
         t <- expr
         return (SFix i (f,fty) vars t)

letpar :: P STerm
letpar = do
  i <- getPos
  reserved "let"
  (v,ty) <- parens binding
  reservedOp "="  
  def <- expr
  reserved "in"
  body <- expr
  return (SLet i (v,ty) def body)

letnoparVar :: P (Name, Ty, STerm)
letnoparVar = do
  v <- var
  reservedOp ":"
  ty <- typeP
  reservedOp "="
  def <- expr
  return (v, ty, def)

getVarsTypes :: [(Name, Ty)] -> Ty -> Ty
getVarsTypes [] tyf = NatTy -- 
getVarsTypes [(v,ty)] tyf = FunTy ty tyf
getVarsTypes ((v,ty):vs) tyf = FunTy ty (getVarsTypes vs tyf)

letnoparFun :: P (Name, Ty, STerm)
letnoparFun = do
  vf <- var
  vars <- binders
  reservedOp ":"
  tyf <- typeP
  reservedOp "="
  def <- expr
  let ty = getVarsTypes vars tyf
  return (vf, ty, SLam NoPos vars def)

letnoparrec :: P (Name, Ty, STerm)
letnoparrec = do
  i <- getPos
  reserved "rec"
  v <- var
  vars <- binders
  reservedOp ":"
  ty <- typeP
  reservedOp "="
  def <- expr
  let tyf = getVarsTypes vars ty
  return (v, tyf, SFix NoPos (v,tyf) vars def)

letnopar :: P STerm
letnopar = do
  i <- getPos
  reserved "let"
  (v,ty,def) <- try letnoparVar <|> letnoparFun <|> letnoparrec
  reserved "in"
  body <- expr
  return (SLet i (v,ty) def body)

-- letrec :: P STerm
-- letrec = do
--   i <- getPos
--   reserved "let"
--   reserved "rec"
--   v <- var
--   vars <- binders
--   reservedOp ":"
--   ty <- typeP
--   reservedOp "="
--   def <- expr
--   reserved "in"
--   body <- expr
--   return (SLet i (v,ty) (SFix NoPos (v,ty) vars def) body)

letexp :: P STerm
letexp = do
  try letpar <|> letnopar

-- | Parser de términos
tm :: P STerm
tm = app <|> lam <|> ifz <|> printOp <|> fix <|> letexp

-- | Parser de declaraciones
decl :: P (Decl STerm)
decl = do 
     i <- getPos
     reserved "let"
     v <- var
     reservedOp "="
     t <- expr
     return (Decl i v t)

-- | Parser de programas (listas de declaraciones) 
program :: P [Decl STerm]
program = many decl

-- | Parsea una declaración a un término
-- Útil para las sesiones interactivas
declOrTm :: P (Either (Decl STerm) STerm)
declOrTm =  try (Left <$> decl) <|> (Right <$> expr)

-- Corre un parser, chequeando que se pueda consumir toda la entrada
runP :: P a -> String -> String -> Either ParseError a
runP p s filename = runParser (whiteSpace *> p <* eof) () filename s

--para debugging en uso interactivo (ghci)
parse :: String -> STerm
parse s = case runP expr s "" of
            Right t -> t
            Left e -> error ("no parse: " ++ show s)
