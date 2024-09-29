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
                           "ifz", "print","type"],
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

tyatom :: P STy
tyatom = (identifier >>= \n-> return (STy n))
         <|> parens typeP

typeP :: P STy
typeP = try (do
          x <- tyatom
          reservedOp "->"
          y <- typeP
          return (SFunTy x y))
      <|> tyatom

const :: P Const
const = CNat <$> num

printNoApp :: P STerm
printNoApp = do
  i <- getPos
  reserved "print"
  str <- option "" stringLiteral
  return (SLam i [("x", (STy "Nat"))] (SPrint i str (SV i "x")))

printApp :: P STerm
printApp = do
  i <- getPos
  reserved "print"
  str <- option "" stringLiteral
  a <- atom
  return (SPrint i str a)

printOp :: P STerm
printOp = do
  try printApp <|> try printNoApp

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

getVarsTypes :: [(Name, Ty)] -> Ty -> Ty
getVarsTypes [] tyf = NatTy -- 
getVarsTypes [(v,ty)] tyf = FunTy ty tyf
getVarsTypes ((v,ty):vs) tyf = FunTy ty (getVarsTypes vs tyf)

binding :: P [(Name, STy)]
binding = do v <- many var
             reservedOp ":"
             ty <- typeP
             return (map (\x -> (x,ty)) v)

parensBinding :: P [(Name, STy)]
parensBinding = parens binding

binders :: P [(Name, STy)]
binders = do arrayVars <- many parensBinding
             return (concat arrayVars)

lam :: P STerm
lam = do i <- getPos
         reserved "fun"
         vars <- binders
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
         fun <- parens binding
         let (f, fty) = head fun
         vars <- binders
         reservedOp "->"
         t <- expr
         return (SFix i (f,fty) vars t)

letpar :: P STerm
letpar = do
  i <- getPos
  reserved "let"
  vars <- parens binding
  let (v, ty) = head vars
  reservedOp "="
  def <- expr
  reserved "in"
  body <- expr
  return (SLet i LVar [(v,ty)] def body)

letVar :: P ([(Name, STy)], STerm, LetType)
letVar = do
  v <- var
  reservedOp ":"
  ty <- typeP
  reservedOp "="
  def <- expr
  return ([(v, ty)], def, LVar)

letFun :: P ([(Name, STy)], STerm, LetType)
letFun = do
  v <- var
  vars <- binders
  reservedOp ":"
  ty <- typeP
  reservedOp "="
  def <- expr
  return ((v,ty):vars, def, LFun)

letRec :: P ([(Name, STy)], STerm, LetType)
letRec = do
  i <- getPos
  reserved "rec"
  v <- var
  vars <- binders
  reservedOp ":"
  ty <- typeP
  reservedOp "="
  def <- expr
  return ((v,ty):vars, def, LRec)

letnopar :: P STerm
letnopar = do
  i <- getPos
  reserved "let"
  (vars,def, lt) <- try letVar <|> try letFun <|> try letRec
  reserved "in"
  body <- expr
  return (SLet i lt vars def body)


letexp :: P STerm
letexp = do
  try letpar <|> letnopar

-- | Parser de términos
tm :: P STerm
tm = app <|> lam <|> ifz <|> printOp <|> fix <|> letexp

declfun :: P ([(Name, STy)], STerm, LetType)
declfun = do
  v <- var
  vars <- binders
  reservedOp ":"
  ty <- typeP
  reservedOp "="
  t <- expr
  return ((v, ty):vars, t, LFun)

declvar :: P ([(Name, STy)], STerm, LetType)
declvar = do
  v <- var
  reservedOp ":"
  ty <- typeP
  reservedOp "="
  t <- expr
  return ([(v, ty)], t, LVar)

declrec :: P ([(Name, STy)], STerm, LetType)
declrec = do
  reserved "rec"
  v <- var
  vars <- binders
  reservedOp ":"
  ty <- typeP
  reservedOp "="
  t <- expr
  return ((v, ty):vars, t, LRec)

-- type funfun = fun -> fun
-- type fun =  Nat -> Nat
typeDecl :: P (Decl STy)
typeDecl = do
  i <- getPos
  reserved "type"
  ty <- tyIdentifier
  reservedOp "="
  tydef <- typeP
  return Decl {declPos = i, declName = ty, declBody = tydef }

-- | Parser de declaraciones
decl :: P (SDecl STerm)
decl = do
    i <- getPos
    reserved "let"
    (vars, term, t) <- try declvar <|> try declfun <|> try declrec
    return (SDecl i vars t term)

-- | Parser de programas (listas de declaraciones) 
program :: P [Either (SDecl STerm) (Decl STy)]
program = many (try (Left <$> decl) <|> try (Right <$> typeDecl))


-- | Parsea una declaración a un término
-- Útil para las sesiones interactivas
declOrTm :: P (Either (Either (SDecl STerm) (Decl STy)) STerm)
declOrTm =  try (Right <$> expr) <|> (try (Left . Left <$> decl) <|> (Left . Right <$> typeDecl))

-- Corre un parser, chequeando que se pueda consumir toda la entrada
runP :: P a -> String -> String -> Either ParseError a
runP p s filename = runParser (whiteSpace *> p <* eof) () filename s

--para debugging en uso interactivo (ghci)
parse :: String -> STerm
parse s = case runP expr s "" of
            Right t -> t
            Left e -> error ("no parse: " ++ show s)
