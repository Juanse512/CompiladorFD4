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

module Elab ( elab, elabDecl, elabTy) where

import Lang
import Subst
import MonadFD4 ( MonadFD4, lookupDeclTy )
import Data.Data (tyConFingerprint)
-- Obtiene el tipo de una funcion dada la lista de sus variables y lo que devuelve
-- getVarsTypes :: [(Name, Ty)] -> Ty -> Ty
-- getVarsTypes [] tyf = NatTy --
-- getVarsTypes [(v,ty)] tyf = FunTy ty tyf
-- getVarsTypes ((v,ty):vs) tyf = FunTy ty (getVarsTypes vs tyf)
-- Obtiene el tipo de una funcion dada la lista de sus variables y lo que devuelve
getVarsTypes :: [(Name, STy)] -> STy -> STy
getVarsTypes [] tyf = STy "Nat" -- 
getVarsTypes [(v,ty)] tyf = SFunTy ty tyf
getVarsTypes ((v,ty):vs) tyf = SFunTy ty (getVarsTypes vs tyf)
-- getVarsTypes ((v,ty):vs) tyf = SFunTy (getVarsTypes vs tyf) ty 


-- | 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado. 
elabTy :: MonadFD4 m => STy -> m Ty
elabTy (STy n) = do x <- lookupDeclTy n
                    case x of
                      Just ty -> return ty
                      Nothing -> error $ "No se encontró el tipo " ++ n
elabTy (SFunTy st1 st2) = do t1 <- elabTy st1
                             t2 <- elabTy st2
                             return $ FunTy t1 t2

elab :: MonadFD4 m => STerm -> m Term
elab = elab' []

elab' :: MonadFD4 m => [Name] -> STerm -> m Term
elab' env (SV p v) = if v `elem` env
                     then return $ V p (Free v)
                     else return $ V p (Global v)
  -- Tenemos que ver si la variable es Global o es un nombre local
  -- En env llevamos la lista de nombres locales.

elab' _ (SConst p c) = return $ Const p c
elab' env (SLam p [(v,sty)] st) = do t <- elab' (v:env) st
                                     ty <- elabTy sty
                                     return $ Lam p v ty (close v t)

elab' env (SLam p vars st) = do let (x,xsty) = head vars
                                t <- elab' (x:env) (SLam p (tail vars) st)
                                xty <- elabTy xsty
                                return $ Lam p x xty (close x t)

elab' env (SFix p (f,fsty) [(x,xsty)] st) = do t <- elab' (x:f:env) st
                                               xty <- elabTy xsty
                                               fty <- elabTy fsty
                                               return $ Fix p f fty x xty (close2 f x t)
elab' env (SFix p (f,fsty) vars st) = do let (x,xsty) = head vars
                                         t <- elab' (x:f:env) (SFix p (f,fsty) (tail vars) st)
                                         xty <- elabTy xsty
                                         fty <- elabTy fsty
                                         return $ Fix p f fty x xty (close2 f x t)

elab' env (SIfZ p sc st se)         = do c <- elab' env sc
                                         t <- elab' env st
                                         e <- elab' env se
                                         return $ IfZ p c t e
-- Operadores binarios
elab' env (SBinaryOp i o st su) = do t <- elab' env st
                                     u <- elab' env su
                                     return $ BinaryOp i o t u
-- Operador Print
elab' env (SPrint i str st) = do t <- elab' env st
                                 return $ Print i str t
-- Aplicaciones generales
elab' env (SApp p sh sa) = do h <- elab' env sh
                              a <- elab' env sa
                              return $ App p h a

elab' env (SLet p LVar vars sdef sbody) = do let (v,svty) = head vars
                                             vty <- elabTy svty
                                             def <- elab' env sdef
                                             body <- elab' (v:env) sbody
                                             return $ Let p v vty def (close v body)

elab' env (SLet p LFun vars sdef sbody) = do let (v,svty) = head vars
                                             tyf <- elabTy (getVarsTypes (tail vars) svty)
                                             def <- elab' env (SLam p (tail vars) sdef)
                                             body <- elab' (v:env) sbody
                                             return $ Let p v tyf def (close v body)
  -- let (v,vty) = head vars
  -- in Let p v (getVarsTypes (tail vars) vty) (elab' env (SLam p (tail vars) def)) (close v (elab' (v:env) body))


elab' env (SLet p LRec vars sdef sbody) = do let (v,svty) = head vars
                                             let styf = getVarsTypes (tail vars) svty
                                             tyf <- elabTy styf
                                             def <- elab' env (SFix p (v, styf) (tail vars) sdef)
                                             body <- elab' (v:env) sbody
                                             return $ Let p v tyf def (close v body)

elabDecl :: MonadFD4 m => SDecl STerm -> m (Decl Term)
-- elabDecl (SDecl p vars LVar t) = let (v,ty) = head vars
--                                  in Decl p v (elab t)
elabDecl (SDecl p vars LVar st) = do let (v,ty) = head vars
                                     t <- elab st
                                     return $ Decl p v t


elabDecl (SDecl p vars LFun t) = do let (v,ty) = head vars
                                    elb <- elab (SLam p (tail vars) t)
                                    return $ Decl p v elb
-- elabDecl (SDecl p vars LFun t) = let (v,ty) = head vars
--                                  in Decl p v (elab (SLam p (tail vars) t))

elabDecl (SDecl p vars LRec t) = do let (v,ty) = head vars
                                    let tyf = getVarsTypes (tail vars) ty
                                    elb <- elab (SFix p (v, tyf) (tail vars) t)
                                    return $ Decl p v elb
