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
import PPrint
import Eval 
import Common 
import Subst


data Val = VN Int | VClos Clos
    deriving Show

type Env = [Val]

data Clos = 
    ClosFun Env TTerm
    | ClosFix Env TTerm
    deriving Show

data Frame = 
    KArg Env TTerm
    | KClos Clos
    | KIfz Env TTerm TTerm
    | KOpL Env BinaryOp TTerm
    | KOpR Val BinaryOp 
    | KPrint String
    | KLet Env TTerm
    deriving Show

type Kont = [Frame]


search :: MonadFD4 m => TTerm -> Env -> Kont -> m Val
search (Print _ s t) p k = search t p (KPrint s : k)
search (BinaryOp _ op t u) p k = search t p (KOpL p op u : k)
search (IfZ _ c t u) p k = search c p (KIfz p t u : k)
search (App _ t u) p k = search t p (KArg p u : k)
search (Const _ (CNat n)) p k = destroy (VN n) k
search (Lam _ x _ (Sc1 t)) p k = destroy (VClos (ClosFun p t)) k
search (Fix _ _ _ _ _ (Sc2 t)) p k = destroy (VClos (ClosFix p t)) k
search (Let _ name _ value (Sc1 t)) p k = search value p (KLet p t : k)



destroy :: MonadFD4 m => Val -> Kont -> m Val
destroy v@(VN n) (KPrint s : k) = printFD4 (s ++ " " ++ show n) >> destroy v k
destroy v@(VN n) (KOpL p op u : k) = search u p (KOpR v op : k)
destroy (VN n) (KOpR (VN m) op : k) = destroy (VN (semOp op m n)) k
destroy (VN 0) (KIfz p t e : k) = search t p k
destroy (VN _) (KIfz p t e : k) = search e p k 
destroy (VClos clos) (KArg p t : k) = search t p (KClos clos : k)
destroy v (KClos (ClosFun p t) : k) = search t (v : p) k
destroy v (KClos f@(ClosFix p t) : k) = search t (v : VClos f : p) k
destroy v (KLet p t : k) = search t (v : p) k
destroy v [] = return v
destroy _ _ = undefined

-- [1, 2]
-- Bound 0 + Bound 1
-- 1 + Bound 0
-- [2]
-- 1 + 2
-- []

valToTTerm :: Val -> TTerm
valToTTerm (VN n) = Const (NoPos, NatTy) (CNat n)
valToTTerm (VClos (ClosFun [] t)) = t
valToTTerm (VClos (ClosFun p t)) = valToTTerm (VClos (ClosFun (tail p) (subst (valToTTerm (head p)) (Sc1 t))))
valToTTerm (VClos (ClosFix p t)) = valToTTerm (VClos (ClosFix (tail (tail p)) (subst2 (valToTTerm (head p)) (valToTTerm (head (tail p))) (Sc2 t)) ))
-- valToTTerm (VClos (ClosFun p (Sc1 t))) = subst (map valToTTerm p) t
-- valToTTerm (VClos (ClosFix p (Sc1 t))) = subst2 (map valToTTerm p) (map valToTTerm p) t

evalCEK :: MonadFD4 m => TTerm -> m TTerm
evalCEK t = do
    v <- search t [] []
    return $ valToTTerm v

        