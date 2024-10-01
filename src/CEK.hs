{-|
Module      : CEK
Description : Algunas operaciones generales
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}
-- Lam --- scope
-- ClosFun scope 

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
    ClosFun (Pos, Ty) Env Name Ty TTerm
    | ClosFix (Pos,Ty) Env Name Ty Name Ty TTerm
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
search (Lam i x ty (Sc1 t)) p k = destroy (VClos (ClosFun i p x ty t)) k
search (Fix i x1 t1 x2 t2 (Sc2 t)) p k = destroy (VClos (ClosFix i p x1 t1 x2 t2 t)) k
search (Let _ name _ value (Sc1 t)) p k = search value p (KLet p t : k)
search (V _ (Bound n)) p k = destroy (p !! n) k
search (V _ (Free n)) p k = failFD4 $ "Variable " ++ n ++ " no definida"
search (V _ (Global n)) p k = do 
    v <- lookupDecl n
    case v of
        Just t -> search t p k
        Nothing -> failFD4 $ "Variable " ++ n ++ " no definida"


destroy :: MonadFD4 m => Val -> Kont -> m Val
destroy v@(VN n) (KPrint s : k) = printFD4 (s ++ show n) >> destroy v k
destroy v@(VN n) (KOpL p op u : k) = search u p (KOpR v op : k)
destroy (VN n) (KOpR (VN m) op : k) = destroy (VN (semOp op m n)) k
destroy (VN 0) (KIfz p t e : k) = search t p k
destroy (VN _) (KIfz p t e : k) = search e p k 
destroy (VClos clos) (KArg p t : k) = search t p (KClos clos : k)
destroy v (KClos (ClosFun _ p _ _ t) : k) = search t (v : p) k
destroy v (KClos f@(ClosFix _ p _ _ _ _ t) : k) = search t (v : VClos f : p) k
destroy v (KLet p t : k) = search t (v : p) k
destroy v [] = return v
destroy _ _ = undefined

-- [1, 2]
-- Bound 0 + Bound 1
-- 1 + Bound 0
-- [2]
-- 1 + 2
-- []

-- valToTTerm :: Val -> TTerm
-- valToTTerm (VN n) = Const (NoPos, NatTy) (CNat n)
-- valToTTerm (VClos (ClosFun i [] x ty t)) = Lam i x ty (Sc1 t)
-- valToTTerm (VClos (ClosFun i p x ty t)) = valToTTerm (VClos (ClosFun i (tail p) x ty (subst (valToTTerm (head p)) (Sc1 t))))
-- valToTTerm (VClos (ClosFix i [] x1 t1 x2 t2 t)) = Fix i x1 t1 x2 t2 (Sc2 t)
-- valToTTerm (VClos (ClosFix i p x1 t1 x2 t2 t)) = valToTTerm (VClos (ClosFix i (tail (tail p)) x1 t1 x2 t2 (subst2 (valToTTerm (head p)) (valToTTerm (head (tail p))) (Sc2 t)) ))

valToTTerm :: Val -> TTerm
valToTTerm (VN c) = Const (NoPos, NatTy) (CNat c)
valToTTerm (VClos (ClosFun info p x ty tm)) = substN (map valToTTerm p) $ Lam info x ty (Sc1 tm)
valToTTerm (VClos (ClosFix info p f fty x xty tm)) = substN (map valToTTerm p) $ Fix info f fty x xty (Sc2 tm)

evalCEK :: MonadFD4 m => TTerm -> m TTerm
evalCEK t = do
    v <- search t [] []
    return $ valToTTerm v

        