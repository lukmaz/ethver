module AuxPrismEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map

import AbsEthver
import ConstantsEthver

maxRealValueOfType :: Type -> Exp
maxRealValueOfType (TUInt x) = EInt (x - 1)
maxRealValueOfType (TRUInt x) = EInt (x - 1)
maxRealValueOfType TBool = ETrue

maxTypeExpOfType :: Type -> Exp
maxTypeExpOfType (TUInt x) = EInt (x - 1)
maxTypeExpOfType (TRUInt x) = EInt x
maxTypeExpOfType TBool = ETrue

maxTypeValueOfType :: Type -> Integer
maxTypeValueOfType (TUInt x) = (x - 1)
maxTypeValueOfType (TRUInt x) = x
maxTypeValueOfType TBool = 1

-- identFromComp

identFromComp :: Exp -> Ident

identFromComp (EEq (EVar i) v) = i
identFromComp (ENe (EVar i) v) = i
identFromComp (EGt (EVar i) v) = i
identFromComp (EGe (EVar i) v) = i
identFromComp (ELt (EVar i) v) = i
identFromComp (ELe (EVar i) v) = i

identFromComp e = error $ "Cannot extract ident from expression: " ++ (show e)

-- isLeftComp
isLeftComp :: Exp -> Bool

isLeftComp (EEq (EVar _) _) = True
isLeftComp (ENe (EVar _) _) = True
isLeftComp _ = False

-------------
--makeLeft --
-------------

makeLeft :: Exp -> Exp

-- EEq, ENe
makeLeft (EEq (EVar i) v) = EEq (EVar i) v
makeLeft (ENe (EVar i) v) = ENe (EVar i) v
makeLeft (EEq v (EVar i)) = EEq (EVar i) v
makeLeft (ENe v (EVar i)) = ENe (EVar i) v

makeLeft (EEq ESender v) = EEq ESender v
makeLeft (ENe ESender v) = ENe ESender v
makeLeft (EEq v ESender) = EEq ESender v
makeLeft (ENe v ESender) = ENe ESender v

makeLeft (EEq (EArray i e) v) = EEq (EArray i e) v
makeLeft (ENe (EArray i e) v) = ENe (EArray i e) v
makeLeft (EEq v (EArray i e)) = EEq (EArray i e) v
makeLeft (ENe v (EArray i e)) = ENe (EArray i e) v

-- EGt, EGe, ELt, ELe
makeLeft exp@(EGt _ _) = exp
makeLeft exp@(EGe _ _) = exp
makeLeft exp@(ELt _ _) = exp
makeLeft exp@(ELe _ _) = exp

-- ENot, EOr, EAnd
makeLeft (ENot exp) = ENot (makeLeft exp)
makeLeft (EOr e1 e2) = EOr (makeLeft e1) (makeLeft e2)
makeLeft (EAnd e1 e2) = EAnd (makeLeft e1) (makeLeft e2)

-- EVar
makeLeft exp@(EVar _) = exp

-----------------
-- negate cond --
-----------------
negateExp :: Exp -> Exp

negateExp ETrue = EFalse
negateExp EFalse = ETrue

negateExp (EEq e1 e2) = (ENe e1 e2)
negateExp (ENe e1 e2) = (EEq e1 e2)
negateExp (ELt e1 e2) = (EGe e1 e2)
negateExp (ELe e1 e2) = (EGt e1 e2)
negateExp (EGt e1 e2) = (ELe e1 e2)
negateExp (EGe e1 e2) = (ELt e1 e2)

negateExp exp = ENot exp


unident :: Ident -> String
unident (Ident ident) = ident

-- TODO: Only support types with minimal value 0

generateValsList :: Exp -> [Arg] -> [[Exp]]
generateValsList maxValVal args =
  let maxVals = maxValVal:(map (\(Ar typ _) -> maxRealValueOfType typ) args) in
    generateAllVals maxVals

generateValsListNoVal :: [Arg] -> [[Exp]]
generateValsListNoVal args =
  let maxVals = (map (\(Ar typ _) -> maxRealValueOfType typ) args) in
    generateAllVals maxVals

generateAllVals :: [Exp] -> [[Exp]]
generateAllVals [] = []

generateAllVals [ETrue] =
  map (\a -> [a]) [EFalse, ETrue]

generateAllVals [EInt h] =
  map (\a -> [EInt a]) [0..h]

generateAllVals (ETrue:t) =
  let vt = generateAllVals t in
    foldl
      (\acc x ->
        (map (\v -> x:v) vt)
          ++ acc)
      []
      (reverse [ETrue, EFalse])

generateAllVals ((EInt h):t) =
  let vt = generateAllVals t in
    foldl
      (\acc x ->
        (map (\v -> (EInt x):v) vt)
          ++ acc)
      []
      (reverse [0..h])

getArgNames :: Function -> [Arg]
getArgNames (Fun _ args _) = args
getArgNames (FunR _ args _ _) = args

expFromBool :: Bool -> Exp
expFromBool True = ETrue
expFromBool False = EFalse

expFromInt :: Integer -> Exp
expFromInt x = EInt x

intFromExp :: Exp -> Maybe Integer
intFromExp (EInt x) = Just x
intFromExp _ = Nothing
