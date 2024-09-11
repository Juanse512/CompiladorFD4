{-|
Module      : Elab
Description : Elabora un término fully named a uno locally closed.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite elaborar términos y declaraciones para convertirlas desde
fully named (@STerm) a locally closed (@Term@)
-}

module Elab ( elab, elabDecl) where

import Lang
import Subst

-- Obtiene el tipo de una funcion dada la lista de sus variables y lo que devuelve
getVarsTypes :: [(Name, Ty)] -> Ty -> Ty
getVarsTypes [] tyf = NatTy -- 
getVarsTypes [(v,ty)] tyf = FunTy ty tyf
getVarsTypes ((v,ty):vs) tyf = FunTy ty (getVarsTypes vs tyf)


-- | 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado. 
elab :: STerm -> Term
elab = elab' []

elab' :: [Name] -> STerm -> Term
elab' env (SV p v) =
  -- Tenemos que ver si la variable es Global o es un nombre local
  -- En env llevamos la lista de nombres locales.
  if v `elem` env 
    then  V p (Free v)
    else V p (Global v)

elab' _ (SConst p c) = Const p c
elab' env (SLam p [] t) = Lam p "" NatTy (close "" (elab' env t))
elab' env (SLam p [(v,ty)] t) = Lam p v ty (close v (elab' (v:env) t))
elab' env (SLam p ((v,ty):vs) t) = Lam p v ty (close v (elab' (v:env) (SLam p vs t)))
-- elab' env (SLam p (v,ty) t) = Lam p v ty (close v (elab' (v:env) t))
elab' env (SFix p (f,fty) [(x,xty)] t) = Fix p f fty x xty (close2 f x (elab' (x:f:env) t))
elab' env (SFix p (f,fty) ((x,xty):xs) t) = Fix p f fty x xty (close2 f x (elab' (x:f:env) (SLam p xs t)))
-- elab' env (SFix p (f,fty) (x,xty) t) = Fix p f fty x xty (close2 f x (elab' (x:f:env) t))
elab' env (SIfZ p c t e)         = IfZ p (elab' env c) (elab' env t) (elab' env e)
-- Operadores binarios
elab' env (SBinaryOp i o t u) = BinaryOp i o (elab' env t) (elab' env u)
-- Operador Print
elab' env (SPrint i str t) = Print i str (elab' env t)
-- Aplicaciones generales
elab' env (SApp p h a) = App p (elab' env h) (elab' env a)

elab' env (SLet p LVar [(v,vty)] def body) =  
  Let p v vty (elab' env def) (close v (elab' (v:env) body))

elab' env (SLet p LFun ((v,vty):vs) def body) =
  Let p v (getVarsTypes vs vty) (elab' env (SLam p vs def)) (close v (elab' (v:env) body))

elab' env (SLet p LRec ((v,vty):vs) def body) =
  let tyf = getVarsTypes vs vty
  in Let p v tyf (elab' env (SFix p (v, tyf) vs def)) (close v (elab' (v:env) body))
    
-- Nat -> Nat -> Nat
-- Nat  -> (Nat -> Nat)
-- elab' env (SLet p lt (v,vty) def body) =  
--   Let p v vty (elab' env def) (close v (elab' (v:env) body))

elabDecl :: SDecl STerm -> Decl Term
elabDecl (SDecl p [(v, ty)] LVar t) = Decl p v (elab t)
elabDecl (SDecl p ((v, ty):vs) LFun t) = Decl p v (elab (SLam p vs t))
elabDecl (SDecl p ((v, ty):vs) LRec t) = 
  let tyf = getVarsTypes vs ty
  in Decl p v (elab (SFix p (v, tyf) vs t))

-- elabDecl :: Decl STerm -> Decl Term
-- elabDecl = fmap elab

-- let f (x: X) (x: Y) : Z = x + y <- input
-- 