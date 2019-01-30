module AuxPrismEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map

import AbsEthver
import AuxEthver
import ConstantsEthver

maxRealValueOfType :: Type -> Exp
maxRealValueOfType (TUInt x) = EInt (x - 1)
-- TODO: only for 2 commitments, take from MAX_COMMITMENTS constant
maxRealValueOfType (TCUInt x) = EInt 1
maxRealValueOfType TBool = ETrue
maxRealValueOfType THash = EInt 1
maxRealValueOfType (TSig _) = error $ "maxRealValueOfType should not be used with TSig _"

maxTypeExpOfType :: Type -> Exp
maxTypeExpOfType (TUInt x) = EInt (x - 1)
maxTypeExpOfType (TCUInt x) = EInt (x + 1)
maxTypeExpOfType TBool = ETrue
maxTypeExpOfType (TSig _) = error $ "maxTypeExpOfType should not be used with TSig _"

maxTypeValueOfType :: Type -> Integer
maxTypeValueOfType (TUInt x) = (x - 1)
maxTypeValueOfType (TCUInt x) = (x + 1)
maxTypeValueOfType TBool = 1
maxTypeValueOfType TAddr = 1
maxTypeValueOfType THash = 1
maxTypeValueOfType (TSig _) = error $ "maxTypeValueOfType should not be used with TSig _"

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

negateExp (ENot exp) = exp

negateExp exp = ENot exp


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

generateValueUpdates :: Function -> Integer -> Exp -> [[(Ident, Exp)]]

generateValueUpdates (Fun funName _ _) _ _ = 
  [[]]

generateValueUpdates (FunL _ funName _ _) _ _ =
  [[]]

generateValueUpdates (FunV funName args stms) nr value =
  generateValueUpdates (FunVL (-1) funName args stms) nr value

generateValueUpdates (FunVL _ funName _ _) nr value =
  [[(Ident $ unident funName ++ sValueSuffix ++ (show nr), value)]]
  
expFromBool :: Bool -> Exp
expFromBool True = ETrue
expFromBool False = EFalse

expFromInt :: Integer -> Exp
expFromInt x = EInt x

intFromExp :: Exp -> Maybe Integer
intFromExp (EInt x) = Just x
intFromExp _ = Nothing

getFunName :: Function -> Ident
getFunName (FunVL _ name _ _) = name
getFunName (FunL _ name _ _) = name
getFunName (FunV name _ _) = name
getFunName (Fun name _ _) = name

getFunArgs :: Function -> [Arg]
getFunArgs (FunVL _ _ args _) = args
getFunArgs (FunL _ _ args _) = args
getFunArgs (FunV _ args _) = args
getFunArgs (Fun _ args _) = args

commitmentInArguments :: Function -> Bool

commitmentInArguments (FunV name args stms) = commitmentInArguments (Fun name args stms)
commitmentInArguments (FunL _ name args stms) = commitmentInArguments (Fun name args stms)
commitmentInArguments (FunVL _ name args stms) = commitmentInArguments (Fun name args stms)

commitmentInArguments (Fun _ args _) = 
  any 
    (\arg -> case arg of
      Ar (TCUInt _) _ -> True
      _ -> False
    )
    args

commitmentFromArguments :: Function -> Ident

commitmentFromArguments (FunV name args stms) = commitmentFromArguments (Fun name args stms)
commitmentFromArguments (FunL _ name args stms) = commitmentFromArguments (Fun name args stms)
commitmentFromArguments (FunVL _ name args stms) = commitmentFromArguments (Fun name args stms)

commitmentFromArguments (Fun _ args _) = 
  case filter 
    (\arg -> case arg of
      Ar (TCUInt _) _ -> True
      _ -> False
    )
    args
    of
      [Ar _ varName] -> varName

hashInArguments :: Function -> Bool

hashInArguments (FunV name args stms) = hashInArguments (Fun name args stms)
hashInArguments (FunL _ name args stms) = hashInArguments (Fun name args stms)
hashInArguments (FunVL _ name args stms) = hashInArguments (Fun name args stms)

hashInArguments (Fun _ args _) = 
  any 
    (\arg -> case arg of
      Ar (THash) _ -> True
      _ -> False
    )
    args

signatureInArguments :: Function -> Bool

signatureInArguments (FunV name args stms) = signatureInArguments (Fun name args stms)
signatureInArguments (FunL _ name args stms) = signatureInArguments (Fun name args stms)
signatureInArguments (FunVL _ name args stms) = signatureInArguments (Fun name args stms)

signatureInArguments (Fun _ args _) = 
  any 
    (\arg -> case arg of
      Ar (TSig _) _ -> True
      _ -> False
    )
    args

signatureFromArguments :: Function -> Ident

signatureFromArguments (FunV name args stms) = signatureFromArguments (Fun name args stms)
signatureFromArguments (FunL _ name args stms) = signatureFromArguments (Fun name args stms)
signatureFromArguments (FunVL _ name args stms) = signatureFromArguments (Fun name args stms)

signatureFromArguments (Fun _ args _) = 
  case filter 
    (\arg -> case arg of
      Ar (TSig _) _ -> True
      _ -> False
    )
    args
    of
      [Ar _ varName] -> varName



