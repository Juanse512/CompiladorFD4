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
elab' env (SLam p [(v,ty)] t) = Lam p v ty (close v (elab' (v:env) t))

elab' env (SLam p vars t) = let (x,xty) = head vars
                            in Lam p x xty (close x (elab' (x:env) (SLam p (tail vars) t)))

elab' env (SFix p (f,fty) [(x,xty)] t) = Fix p f fty x xty (close2 f x (elab' (x:f:env) t))
elab' env (SFix p (f,fty) vars t) = let (x,xty) = head vars
                                    in Fix p f fty x xty (close2 f x (elab' (x:f:env) (SLam p (tail vars) t)))

elab' env (SIfZ p c t e)         = IfZ p (elab' env c) (elab' env t) (elab' env e)
-- Operadores binarios
elab' env (SBinaryOp i o t u) = BinaryOp i o (elab' env t) (elab' env u)
-- Operador Print
elab' env (SPrint i str t) = Print i str (elab' env t)
-- Aplicaciones generales
elab' env (SApp p h a) = App p (elab' env h) (elab' env a)


elab' env (SLet p LVar vars def body) = let (v,vty) = head vars
                                        in Let p v vty (elab' env def) (close v (elab' (v:env) body))



elab' env (SLet p LFun vars def body) = 
  let (v,vty) = head vars
  in Let p v (getVarsTypes (tail vars) vty) (elab' env (SLam p (tail vars) def)) (close v (elab' (v:env) body))

    
elab' env (SLet p LRec vars def body) = let (v,vty) = head vars
                                            tyf = getVarsTypes (tail vars) vty
                                        in Let p v tyf (elab' env (SFix p (v, tyf) (tail vars) def)) (close v (elab' (v:env) body))

elabDecl :: SDecl STerm -> Decl Term
elabDecl (SDecl p vars LVar t) = let (v,ty) = head vars
                                 in Decl p v (elab t)



elabDecl (SDecl p vars LFun t) = let (v,ty) = head vars
                                 in Decl p v (elab (SLam p (tail vars) t))

elabDecl (SDecl p vars LRec t) = let (v,ty) = head vars
                                     tyf = getVarsTypes (tail vars) ty
                                 in Decl p v (elab (SFix p (v, tyf) (tail vars) t))
