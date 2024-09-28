{-|
Module      : CEK
Description : Algunas operaciones generales
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}


module CEK where

import Lang
import MonadFD4
import Pprint
import Eval 
import Common 
import Subst


data Val = VN Int | VClos Clos
    deriving Show

type Env = [Val]

data Clos = 
    ClosFun Env TTerm TTerm
    | ClosFix Env TTerm TTerm
    deriving Show

data Frame = 
    KArg Env TTerm
    | KClos Clos
    | KIfz Env TTerm TTerm
    | KOpL Env BinaryOp TTerm
    | KOpR Val BinaryOp 
    | KPrint String
    deriving Show

type Kont = [Frame]


search :: MonadFD4 m => TTerm -> Env -> Kont -> m Val
search (Print _ s t) p k = search t p (KPrint s : k)
search (BinaryOp _ op t u) p k = search t p (KOpL p op u : k)
search (IfZ _ c t e) p k = search c p (KIfz p t u : k)
search (App _ t u) p k = search t p (KArg p u : k)
search (Var _ x) p k = destroy (p !! x) k
search (Const _ n) p k = destroy (VN n) k
search (Lam _ _ _ t) p k = destroy (VClos (ClosFun p t k)) k
search (Fix _ _ _ _ _ t) p k = destroy (VClos (ClosFix p t k)) k


destroy :: MonadFD4 m => Val -> Kont -> m Val
destroy v@(VN n) (KPrint s : k) = printFD4 (s ++ " " ++ show n) >> destroy v k
destroy v@(VN n) (KOpL p op u : k) = search u p (KOpR v op : k)
destroy (VN n) (KOpR (VN m) op : k) = destroy (VN (semOp op m n)) k
destroy (VN 0) (KIfz p t e : k) = search t p k
destroy (VN _) (KIfz p t e : k) = search e p k
destroy (VClos clos) (KArg p t : k) = search t p (KClos clos : k)
destroy v (KClos (ClosFun p t _) : k) = search t (v : p) k
destroy v (KClos f@(ClosFix p t _) : k) = search t (v : VClos f : p) k
destroy v [] = return v
destroy _ _ = undefined


evalCEK :: MonadFD4 m => TTerm -> m TTerm
evalCEK t = do
    v <- search t [] []
    return $ ValToTTerm v
    where 
        ValToTTerm (VN n) = Const NoPos n
        ValToTTerm (VClos (ClosFun p _ f)) = subst (map ValToTTerm p) t
        ValToTTerm (VClos (ClosFix p _ f)) = subst2 (map ValToTTerm p) (map ValToTTerm p) t