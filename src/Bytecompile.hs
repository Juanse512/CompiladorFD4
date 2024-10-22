{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-|
Module      : Bytecompile
Description : Compila a bytecode. Ejecuta bytecode.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite compilar módulos a la Macchina. También provee
una implementación de la Macchina para ejecutar el bytecode.
-}
module Bytecompile
  (Bytecode, runBC, bcWrite, bcRead, bytecompileModule, showBC)
 where

import Lang
import Subst
import MonadFD4

import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Word32, Binary(put, get), decode, encode )
import Data.Binary.Put ( putWord32le )
import Data.Binary.Get ( getWord32le, isEmpty )

import Data.List (intercalate)
import Data.Char

type Opcode = Int
type Bytecode = [Int]
data Val = I Int | Fun Env Bytecode | RA Env Bytecode
type Env = [Val]
type Stack = [Val]

newtype Bytecode32 = BC { un32 :: [Word32] }

{- Esta instancia explica como codificar y decodificar Bytecode de 32 bits -}
instance Binary Bytecode32 where
  put (BC bs) = mapM_ putWord32le bs
  get = go
    where go =
           do
            empty <- isEmpty
            if empty
              then return $ BC []
              else do x <- getWord32le
                      BC xs <- go
                      return $ BC (x:xs)

{- Estos sinónimos de patrón nos permiten escribir y hacer
pattern-matching sobre el nombre de la operación en lugar del código
entero, por ejemplo:

   f (CALL : cs) = ...

 Notar que si hubieramos escrito algo como
   call = 5
 no podríamos hacer pattern-matching con `call`.

 En lo posible, usar estos códigos exactos para poder ejectutar un
 mismo bytecode compilado en distintas implementaciones de la máquina.
-}
pattern NULL     = 0
pattern RETURN   = 1
pattern CONST    = 2
pattern ACCESS   = 3
pattern FUNCTION = 4
pattern CALL     = 5
pattern ADD      = 6
pattern SUB      = 7
pattern FIX      = 9
pattern STOP     = 10
pattern SHIFT    = 11
pattern DROP     = 12
pattern PRINT    = 13
pattern PRINTN   = 14
pattern JUMP     = 15

--función util para debugging: muestra el Bytecode de forma más legible.
showOps :: Bytecode -> [String]
showOps [] = []
showOps (NULL:xs)        = "NULL" : showOps xs
showOps (RETURN:xs)      = "RETURN" : showOps xs
showOps (CONST:i:xs)     = ("CONST " ++  show i) : showOps xs
showOps (ACCESS:i:xs)    = ("ACCESS " ++ show i) : showOps xs
showOps (FUNCTION:i:xs)  = ("FUNCTION len=" ++ show i) : showOps xs
showOps (CALL:xs)        = "CALL" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (SUB:xs)         = "SUB" : showOps xs
showOps (FIX:xs)         = "FIX" : showOps xs
showOps (STOP:xs)        = "STOP" : showOps xs
showOps (JUMP:i:xs)      = ("JUMP off=" ++ show i) : showOps xs
showOps (SHIFT:xs)       = "SHIFT" : showOps xs
showOps (DROP:xs)        = "DROP" : showOps xs
showOps (PRINT:xs)       = let (msg,_:rest) = span (/=NULL) xs
                           in ("PRINT " ++ show (bc2string msg)) : showOps rest
showOps (PRINTN:xs)      = "PRINTN" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (x:xs)           = show x : showOps xs

showBC :: Bytecode -> String
showBC = intercalate "; " . showOps

bcc :: MonadFD4 m => TTerm -> m Bytecode
bcc (Const _ (CNat n)) return [CONST n]
bcc (BinaryOp _ Add t u) = do
  bc1 <- bcc t
  bc2 <- bcc u
  return $ bc1 ++ bc2 ++ [ADD]
bcc (BinaryOp _ Sub t u) = do
  bc1 <- bcc t
  bc2 <- bcc u
  return $ bc1 ++ bc2 ++ [SUB]
bcc (V _ (Bound i)) = return [ACCESS, i]
bcc (V _ (Free _)) = failFD4 "Flashiaste Free!" 
bcc (V _ (Global _)) = failFD4 "Flashiaste Global!"
bcc (App _ t u) = do
  bc1 <- bcc t
  bc2 <- bcc u
  return $ bc1 ++ bc2 ++ [CALL]
bcc (Lam _ _ _ t) = do
  bc1 <- bcc t
  return $ [FUNCTION] ++ [(length bc1 + 1)] ++ bc1 ++ [RETURN]
bcc (Let _ _ t u) = do
  bc1 <- bcc t
  bc2 <- bcc u
  return $ bc1 ++ [SHIFT] ++ bc2 ++ [DROP]
bcc (Print _ s t) = do
  bc1 <- bcc t
  return $ [PRINTT] ++ (string2bc s) ++ [NULL] ++ bc1 ++ [PRINTN]
bcc (Fix _ _ _ _ t) = do
  bc1 <- bcc t
  return $ [FIX] ++ [(length bc1 + 1)] ++ bc1 ++ [RETURN]
bcc (IfZ _ c t1 t2) = do
  bc1 <- bcc c
  bc2 <- bcc t1
  bc3 <- bcc t2
  return $ bc1 ++ [JUMP] ++ [(length bc2)] ++ [(length bc3)] ++ bc2 ++ bc3

-- bcc t = failFD4 "implementame!"

globalToFree :: TTerm -> TTerm
globalToFree (V p (Global i)) = (V p (Free i))
globalToFree _ = _

-- ord/chr devuelven los codepoints unicode, o en otras palabras
-- la codificación UTF-32 del caracter.
string2bc :: String -> Bytecode
string2bc = map ord

bc2string :: Bytecode -> String
bc2string = map chr

bytecompileModule :: MonadFD4 m => Module -> m Bytecode
bytecompileModule m = do
  m' <- map $ (fmap $ (fmap globalToFree)) m
  bc <- bytecompileModule' m'
  return $ bc ++ [STOP]
  where
    bytecompileModule' :: MonadFD4 m => Module -> m Bytecode
    bytecompileModule [] = return []
    bytecompileModule ((Decl _ _ b):m) = do 
      bc1 <- bcc b
      bc2 <- bytecompileModule m
      return $ bc1 ++ [SHIFT] ++ bc2 ++ [DROP]

-- | Toma un bytecode, lo codifica y lo escribe un archivo
bcWrite :: Bytecode -> FilePath -> IO ()
bcWrite bs filename = BS.writeFile filename (encode $ BC $ fromIntegral <$> bs)

---------------------------
-- * Ejecución de bytecode
---------------------------

-- | Lee de un archivo y lo decodifica a bytecode
bcRead :: FilePath -> IO Bytecode
bcRead filename = (map fromIntegral <$> un32) . decode <$> BS.readFile filename

runBC' :: MonadFD4 m => Bytecode -> Env -> Stack -> m ()
runBC' (ACCESS:i:c) e s = runBC' c e (e!!i : s) 
runBC' (CALL:c) e (v:(Fun ef cf):s) = runBC' cf (v:ef) ((RA e c) : s)
runBC' (FUNCTION : l : c) e s = runBC' (drop l c) e ((Fun e (take l c)) : s)
runBC' (RETURN:_) _ (v:(RA e c):s) = runBC' c e (v:s)
runBC' (SHIFT:c) e (v:s) = runBC' c (v:e) s
runBC' (DROP:c) (v:e) s = runBC' c e (v:s)
runBC' (PRINTN : c) e s@(I n : _) = printFD4 (show n) >> runBC' c e s

runBC' (JUMP : l1 : l2 : c) e (0:s) = runBC' (drop l1 c) e s 
runBC' (JUMP : l1 : l2 : c) e (n:s) = do let c' = drop (l1+l2) c 
                                         runBC' (take l1 c):c' e s
-- else runBC' (drop l1 c) e (tail s)
runBC :: MonadFD4 m => Bytecode -> m ()
runBC bs = runBC' bs [] []
