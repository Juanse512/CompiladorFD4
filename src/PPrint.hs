{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use record patterns" #-}
{-|
Module      : PPrint
Description : Pretty printer para FD4.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module PPrint (
    pp,
    ppTy,
    ppName,
    ppDecl
    ) where

import Lang
import Subst ( open, open2 )
import Common ( Pos )

import Data.Text ( unpack )
import Prettyprinter.Render.Terminal
  ( renderStrict, italicized, color, colorDull, Color (..), AnsiStyle )
import Prettyprinter
    ( (<+>),
      annotate,
      defaultLayoutOptions,
      layoutSmart,
      nest,
      sep,
      parens,
      Doc,
      Pretty(pretty) )
import MonadFD4 ( gets, MonadFD4 )
import Global ( GlEnv(glb) )

freshen :: [Name] -> Name -> Name
freshen ns n = let cands = n : map (\i -> n ++ show i) [0..]
               in head (filter (`notElem` ns) cands)

prettyFunction :: STerm -> ([(Name, STy)], STerm)
prettyFunction (SLam _ x t) = (x, t)
prettyFunction t = ([], t)

getReturnType :: STy -> [(Name, STy)] -> STy
getReturnType ty [] = ty
getReturnType (SFunTy ty tyf) ((_,ty'):xs) = getReturnType tyf xs
getReturnType ty xs = ty

toSTy :: Ty -> STy
toSTy NatTy = STy "Nat"
toSTy (FunTy ty1 ty2) = SFunTy (toSTy ty1) (toSTy ty2)

-- | 'openAll' convierte términos locally nameless
-- a términos fully named abriendo todos las variables de ligadura que va encontrando
-- Debe tener cuidado de no abrir términos con nombres que ya fueron abiertos.
-- Estos nombres se encuentran en la lista ns (primer argumento).
openAll :: (i -> Pos) -> [Name] -> Tm i Var -> STerm
openAll gp ns (V p v) = case v of
      Bound i ->  SV (gp p) $ "(Bound "++show i++")" --este caso no debería aparecer
                                               --si el término es localmente cerrado
      Free x -> SV (gp p) x
      Global x -> SV (gp p) x
openAll gp ns (Const p c) = SConst (gp p) c
openAll gp ns (Lam p x ty t) =
  let
    x' = freshen ns x
    sterm = openAll gp (x':ns) (open x' t)
    sty = toSTy ty
    (vars, body) = prettyFunction sterm
  in SLam (gp p) ((x', sty):vars) body

openAll gp ns (App p t u) = SApp (gp p) (openAll gp ns t) (openAll gp ns u)
openAll gp ns (Fix p f fty x xty t) =
  let
    x' = freshen ns x
    f' = freshen (x':ns) f
    sterm = openAll gp (f':x':ns) (open2 f' x' t)
    fsty = toSTy fty
    xsty = toSTy xty
    (vars, body) = prettyFunction sterm
  in SFix (gp p) (f',fsty) ((x',xsty):vars) body

openAll gp ns (IfZ p c t e) = SIfZ (gp p) (openAll gp ns c) (openAll gp ns t) (openAll gp ns e)
openAll gp ns (Print p str t) = SPrint (gp p) str (openAll gp ns t)
openAll gp ns (BinaryOp p op t u) = SBinaryOp (gp p) op (openAll gp ns t) (openAll gp ns u)


openAll gp ns (Let p v ty m n) =
    let v'= freshen ns v
        defOpened = openAll gp ns m
        sty = toSTy ty
    in case defOpened of
        SLam _ vars t ->
          let (vars', body) = prettyFunction defOpened
          in SLet (gp p) LFun ((v',getReturnType sty vars'):vars') body (openAll gp (v':ns) (open v' n))
        SFix _ (f,fty) vars t ->
          let (vars', body) = prettyFunction t
          in SLet (gp p) LRec ((v',getReturnType sty vars'):vars') body (openAll gp (v':ns) (open v' n))
        _ -> SLet (gp p) LVar [(v',sty)] defOpened (openAll gp (v':ns) (open v' n))

--Colores
constColor :: Doc AnsiStyle -> Doc AnsiStyle
constColor = annotate (color Red)
opColor :: Doc AnsiStyle -> Doc AnsiStyle
opColor = annotate (colorDull Green)
keywordColor :: Doc AnsiStyle -> Doc AnsiStyle
keywordColor = annotate (colorDull Green) -- <> bold)
typeColor :: Doc AnsiStyle -> Doc AnsiStyle
typeColor = annotate (color Blue <> italicized)
typeOpColor :: Doc AnsiStyle -> Doc AnsiStyle
typeOpColor = annotate (colorDull Blue)
defColor :: Doc AnsiStyle -> Doc AnsiStyle
defColor = annotate (colorDull Magenta <> italicized)
nameColor :: Doc AnsiStyle -> Doc AnsiStyle
nameColor = id

-- | Pretty printer de nombres (Doc)
name2doc :: Name -> Doc AnsiStyle
name2doc n = nameColor (pretty n)

-- |  Pretty printer de nombres (String)
ppName :: Name -> String
ppName = id

-- | Pretty printer para tipos (Doc)
ty2doc :: STy -> Doc AnsiStyle
ty2doc (STy s) = typeColor (pretty s)
ty2doc (SFunTy x@(SFunTy _ _) y) = sep [parens (ty2doc x), typeOpColor (pretty "->"),ty2doc y]
ty2doc (SFunTy x y) = sep [ty2doc x, typeOpColor (pretty "->"),ty2doc y]

ty2docTy :: Ty -> Doc AnsiStyle
ty2docTy = ty2doc . toSTy

-- | Pretty printer para tipos (String)
ppTy :: Ty -> String
ppTy = render . ty2docTy

c2doc :: Const -> Doc AnsiStyle
c2doc (CNat n) = constColor (pretty (show n))

binary2doc :: BinaryOp -> Doc AnsiStyle
binary2doc Add = opColor (pretty "+")
binary2doc Sub = opColor (pretty "-")

collectApp :: STerm -> (STerm, [STerm])
collectApp = go [] where
  go ts (SApp _ h tt) = go (tt:ts) h
  go ts h = (h, ts)

parenIf :: Bool -> Doc a -> Doc a
parenIf True = parens
parenIf _ = id

-- t2doc at t :: Doc
-- at: debe ser un átomo
-- | Pretty printing de términos (Doc)
t2doc :: Bool     -- Debe ser un átomo? 
      -> STerm    -- término a mostrar
      -> Doc AnsiStyle
-- Uncomment to use the Show instance for STerm
{- t2doc at x = text (show x) -}
t2doc at (SV _ x) = name2doc x
t2doc at (SConst _ c) = c2doc c
t2doc at (SLam _ vars t) =
  parenIf at $
  sep [ keywordColor (pretty "fun")
      , sep (map binding2doc vars)
      , opColor (pretty "=")
      , nest 2 (t2doc False t)]

t2doc at t@(SApp _ _ _) =
  let (h, ts) = collectApp t in
  parenIf at $
  t2doc True h <+> sep (map (t2doc True) ts)

t2doc at (SFix _ (f,fty) vars m) =
  parenIf at $
  sep [ sep [keywordColor (pretty "fix")
            , binding2doc (f, fty)
            , sep (map binding2doc vars)
            , opColor (pretty "=") ]
      , nest 2 (t2doc False m) ]

t2doc at (SIfZ _ c t e) =
  parenIf at $
  sep [keywordColor (pretty "ifz"), nest 2 (t2doc False c)
     , keywordColor (pretty "then"), nest 2 (t2doc False t)
     , keywordColor (pretty "else"), nest 2 (t2doc False e) ]

t2doc at (SPrint _ str t) =
  parenIf at $
  sep [keywordColor (pretty "print"), pretty (show str), t2doc True t]

t2doc at (SLet _ LFun ((x, xty):xs) t t') =
  parenIf at $
  sep [
    sep [keywordColor (pretty "let")
       , name2doc x
       , sep (map binding2doc xs)
       , pretty ":"
       , ty2doc xty
       , opColor (pretty "=") ]
  , nest 2 (t2doc False t)
  , keywordColor (pretty "in")
  , nest 2 (t2doc False t') ]

t2doc at (SLet _ LRec ((x, xty):xs) t t') =
  parenIf at $
  sep [
    sep [keywordColor (pretty "let")
       , keywordColor (pretty "rec")
       , name2doc x
       , sep (map binding2doc xs)
       , pretty ":"
       , ty2doc xty
       , opColor (pretty "=") ]
  , nest 2 (t2doc False t)
  , keywordColor (pretty "in")
  , nest 2 (t2doc False t') ]

t2doc at (SLet _ LRec [] t t') =
  parenIf at $
  sep [
    sep [keywordColor (pretty "let")
       , keywordColor (pretty "rec")
       , opColor (pretty "=") ]
  , nest 2 (t2doc False t)
  , keywordColor (pretty "in")
  , nest 2 (t2doc False t') ]

t2doc at (SLet _ LVar (x:xs) t t') =
  parenIf at $
  sep [
    sep [keywordColor (pretty "let")
       , binding2doc x
       , opColor (pretty "=") ]
  , nest 2 (t2doc False t)
  , keywordColor (pretty "in")
  , nest 2 (t2doc False t') ]


t2doc at (SLet _ _ [] t t') =
  parenIf at $
  sep [
    sep [keywordColor (pretty "let")
       , opColor (pretty "=") ]
  , nest 2 (t2doc False t)
  , keywordColor (pretty "in")
  , nest 2 (t2doc False t') ]

t2doc at (SBinaryOp _ o a b) =
  parenIf at $
  t2doc True a <+> binary2doc o <+> t2doc True b

binding2doc :: (Name, STy) -> Doc AnsiStyle
binding2doc (x, ty) =
  parens (sep [name2doc x, pretty ":", ty2doc ty])

-- | Pretty printing de términos (String)
pp :: MonadFD4 m => TTerm -> m String
-- Uncomment to use the Show instance for Term
{- pp = show -}
pp t = do
       gdecl <- gets glb
       return (render . t2doc False $ openAll fst (map declName gdecl) t)

render :: Doc AnsiStyle -> String
render = unpack . renderStrict . layoutSmart defaultLayoutOptions

ppDecl :: MonadFD4 m => SDecl STerm -> m String
ppDecl (SDecl p (x:vars) LVar term) = do
  gdecl <- gets glb
  return (render $ sep [defColor (pretty "let")
                       , binding2doc x
                       , defColor (pretty "=")]
                   <+> nest 2 (t2doc False term))


ppDecl (SDecl p ((x,xty):vars) LFun term) = do
  gdecl <- gets glb
  return (render $ sep [defColor (pretty "let")
                       , name2doc x
                       , sep (map binding2doc vars)
                       , pretty ":"
                       , ty2doc xty
                       , defColor (pretty "=")]
                   <+> nest 2 (t2doc False term))


ppDecl (SDecl p ((x,xty):vars) LRec term) = do
  gdecl <- gets glb
  return (render $ sep [defColor (pretty "let")
                       , keywordColor (pretty "rec")
                       , name2doc x
                       , sep (map binding2doc vars)
                       , pretty ":"
                       , ty2doc xty
                       , defColor (pretty "=")]
                   <+> nest 2 (t2doc False term))

ppDecl (SDecl p [] LRec term) = do
  gdecl <- gets glb
  return (render $ sep [defColor (pretty "let")
                       , keywordColor (pretty "rec")
                       , defColor (pretty "=")]
                   <+> nest 2 (t2doc False term))

ppDecl (SDecl p [] _ term) = do
  gdecl <- gets glb
  return (render $ sep [defColor (pretty "let")
                       , defColor (pretty "=")]
                   <+> nest 2 (t2doc False term))