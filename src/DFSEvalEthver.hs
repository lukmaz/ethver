module DFSEvalEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import AbsEthver
import AuxPrismEthver
import AuxWorldPrismEthver
import CodePrismEthver
import ConstantsEthver
import DFSAuxEthver
import WorldPrismEthver

------------------
-- determineStm --
------------------

-- determines values (e.g. array index) from guards


determineStm :: Stm -> Trans -> Stm

determineStm (SAss ident exp) tr = 
  SAss ident (determineExp exp tr)

determineStm (SArrAss ident index exp) tr = 
  SArrAss ident (determineExp index tr) (determineExp exp tr)

------------------
-- determineExp --
------------------

-- used mainly for EArray: showExp(tab[x]) = tab_2 for x = 2
-- uses x value from guards

determineExp :: Exp -> Trans -> Exp
determineExp (EArray (Ident arrName) index) (trName, guards, updates) = 
  case index of
    EInt x ->
      EVar $ Ident $ arrName ++ "_" ++ (show x)
    EVar varName -> do 
      case deduceVarValueFromGuards guards varName of
        (Just (EInt x)) ->
          EVar $ Ident $ arrName ++ "_" ++ (show x)
        Nothing -> 
          error $ "Array index cannot be determined from guards. Array: " ++ (show $ EArray (Ident arrName) index)
            ++ "\nguards: " ++ (show guards)
    _ -> 
      error $ "Array index different than ESender, EInt a, or EVar a"

determineExp (EInt x) _ = EInt x

determineExp (EVar varIdent) (trName, guards, updates) = 
  case deduceVarValueFromGuards guards varIdent of
    (Just (EInt x)) ->
      EInt x
    Nothing ->
      EVar varIdent
      -- chyba musi tak być, bo jak inaczej sobie poradzić z wartością argumentu funkcji?
      --error $ "Value of variable " ++ (show varIdent) ++ " not determined from guards: " ++ (show guards)


-----------------
-- evaluateStm --
-----------------

evaluateStm :: ModifyModuleType -> Stm -> Trans -> VerRes [Trans]

evaluateStm modifyModule (SAss ident exp) tr = do
  trs <- evaluateExp modifyModule exp tr
  return trs

evaluateStm modifyModule (SArrAss ident index exp) tr = do
  trs <- evaluate2Exp modifyModule index exp tr
  return trs

evaluate2Exp :: ModifyModuleType -> Exp -> Exp -> Trans -> VerRes [Trans]
evaluate2Exp modifyModule exp1 exp2 tr = do
  trs <- evaluateExp modifyModule exp1 tr
  foldM
    (\acc tr -> do
      newTrs <- evaluateExp modifyModule exp2 tr
      return $ acc ++ newTrs
    )
    []
    trs

-----------------
-- evaluateExp --
-----------------

evaluateExp :: ModifyModuleType -> Exp -> Trans -> VerRes [Trans]
{-
evaluateExp modifyModule (EOr e1 e2) = evaluateBoolBinOp modifyModule (||) e1 e2 tr
evaluateExp modifyModule (EAnd e1 e2) = evaluateBoolBinOp modifyModule (&&) e1 e2 tr

evaluateExp modifyModule (EEq e1 e2) = evaluateEq modifyModule e1 e2 tr
evaluateExp modifyModule (ENe e1 e2) = do
  tmp <- evaluateEq modifyModule e1 e2 tr
  evaluateBoolUnOp modifyModule not tmp tr

evaluateExp modifyModule (ELt e1 e2) tr = evaluateCompIntBinOp modifyModule (<) e1 e2 tr
evaluateExp modifyModule (ELe e1 e2) tr = evaluateCompIntBinOp modifyModule (<=) e1 e2 tr
evaluateExp modifyModule (EGt e1 e2) tr = evaluateCompIntBinOp modifyModule (>) e1 e2 tr
evaluateExp modifyModule (EGe e1 e2) tr = evaluateCompIntBinOp modifyModule (>=) e1 e2 tr
evaluateExp modifyModule (EAdd e1 e2) tr = evaluateArithmIntBinOp modifyModule (+) e1 e2 tr
evaluateExp modifyModule (ESub e1 e2) tr = evaluateArithmIntBinOp modifyModule (-) e1 e2 tr
evaluateExp modifyModule (EMul e1 e2) tr = evaluateArithmIntBinOp modifyModule (*) e1 e2 tr
evaluateExp modifyModule (EDiv e1 e2) tr = evaluateArithmIntBinOp modifyModule div e1 e2 tr
evaluateExp modifyModule (EMod e1 e2) tr = evaluateArithmIntBinOp modifyModule mod e1 e2 tr

evaluateExp modifyModule (ENeg e) tr = evaluateArithmIntBinOp modifyModule (-) (EInt 0) e tr
evaluateExp modifyModule (ENot e) tr = evaluateBoolUnOp modifyModule not e tr
-}


--DO WYWALENIA?
{-
evaluateExp modifyModule (EArray (Ident ident) index) tr = do
  mod <- modifyModule id
  
  case index of
  
  
  indexEvaluated <- evaluateExp modifyModule index tr
  case indexEvaluated of 
    EInt indexVal -> evaluateExp modifyModule $ EVar $ Ident $ ident ++ "_" ++ (show indexVal)
    _ -> error $ "Index " ++ (show indexEvaluated) ++ " doesn't evaluate to EInt a)"
-}

evaluateExp modifyModule (EArray (Ident arrName) index) (trName, guards, updates) = do
  case index of
    {-
    JAKIES STARE:
    ESender -> do -- TODO: np. trzeba dodać sendera do varsValues
      world <- get
      mod <- modifyModule id
      return $ Map.lookup (whichSender mod) (varsValues world)
    -}
    EInt x -> do
      return [(trName, guards, updates)]
    EVar varIdent -> do 
      case deduceVarValueFromGuards guards varIdent of
        (Just (EInt x)) -> do
          return [(trName, guards, updates)]
        Nothing -> do
          varType <- findVarType varIdent
          case varType of
            Just typ -> do
              let 
                maxVal = maxTypeValueOfType typ
                vals = [0..maxVal]
              return $ map
                  (\val -> 
                    (trName, (EEq (EVar varIdent) (EInt val)):guards, updates) 
                  )
                  vals
            Nothing -> 
              error $ "Var " ++ (unident varIdent) ++ " not found by findVarType"
    _ -> do
      error $ "Array index different than ESender, EInt a, or EVar a"

-- TODO: spora część kodu się pokrywa z evaluateExp (EArray). Może da się połączyć?
evaluateExp modifyModule (EVar varIdent) (trName, guards, updates) = do
  case deduceVarValueFromGuards guards varIdent of
    Just val -> 
      return [(trName, guards, updates)]
    Nothing -> do
      varType <- findVarType varIdent
      case varType of
        Just typ -> do
          let
            maxVal = maxTypeValueOfType typ
            vals = [0..maxVal]
          return $ map
              (\val ->
                (trName, (EEq (EVar varIdent) (EInt val)):guards, updates)
              )
              vals
        Nothing ->
          error $ "Var " ++ (unident varIdent) ++ " type not found by findVarType"

evaluateExp modifyModule (EValue) tr = do
  evaluateExp modifyModule (EVar $ Ident sValue) tr

-- TODO DFS: możliwe, że tu trzeba będzie sprawdzać, czy nie dołożyć sendera do guardsów. albo dodawać zawsze domyślnie
evaluateExp modifyModule ESender tr = do
  world <- get
  mod <- modifyModule id
  case Map.lookup (whichSender mod) (varsValues world) of
    Just x -> return [tr]
    Nothing -> error $ "Variable " ++ (show $ whichSender mod) ++ " not found in varsValues."

evaluateExp modifyModule (EStr name) tr = do
  world <- get
  case Map.lookup name $ playerNumbers world of
    Nothing -> error $ "Player '" ++ name ++ "' not found. (other string constants not supported)"
    Just number -> return [tr]

evaluateExp modifyModule (EInt x) tr = do
  return [tr]

evaluateExp modifyModule ETrue tr = do
  return [tr]

evaluateExp modifyModule EFalse tr = do
  return [tr]


---------------------
-- evaluateExp aux --
---------------------

{-
evaluateBoolBinOp :: ModifyModuleType -> Trans -> (Bool -> Bool -> Bool) -> Exp -> Exp -> VerRes ([Trans], Exp)
evaluateBoolBinOp modifyModule op e1 e2 = do
  v1 <- evaluateExp modifyModule e1
  v2 <- evaluateExp modifyModule e2
  let bool1 = case v1 of
        ETrue -> True
        EFalse -> False
        _ -> error $ "Error in evaluateBoolBinOp: not a bool value: " ++ (show v1)
  let bool2 = case v2 of
        ETrue -> True
        EFalse -> False
        _ -> error $ "Error in evaluateBoolBinOp: not a bool value: " ++ (show v2)
  
  return $ expFromBool $ op bool1 bool2

evaluateArithmIntBinOp :: ModifyModuleType -> Trans -> (Integer -> Integer -> Integer) -> Exp -> Exp -> VerRes ([Trans], Exp)
evaluateArithmIntBinOp modifyModule op e1 e2 = do
  v1 <- evaluateExp modifyModule e1
  v2 <- evaluateExp modifyModule e2
  case intFromExp v1 of 
    Nothing -> error $ "Error in evaluateArithmIntBinOp: not an Int value: " ++ (show v1)
    Just x1 -> case intFromExp v2 of
      Nothing -> error $ "Error in evaluateArithmIntBinOp: not an Int value: " ++ (show v2)
      Just x2 -> return $ expFromInt $ op x1 x2

evaluateCompIntBinOp :: ModifyModuleType -> Trans -> (Integer -> Integer -> Bool) -> Exp -> Exp -> VerRes ([Trans], Exp)
evaluateCompIntBinOp modifyModule op e1 e2 = do
  v1 <- evaluateExp modifyModule e1
  v2 <- evaluateExp modifyModule e2
  case intFromExp v1 of 
    Nothing -> error $ "Error in evaluateCompIntBinOp: not an Int value: " ++ (show v1)
    Just x1 -> case intFromExp v2 of
      Nothing -> error $ "Error in evaluateCompIntBinOp: not an Int value: " ++ (show v2)
      Just x2 -> return $ expFromBool $ op x1 x2

evaluateEq :: ModifyModuleType -> Trans -> Exp -> Exp -> VerRes ([Trans], Exp)
evaluateEq modifyModule e1 e2 = do
  world <- get
  v1 <- evaluateExp modifyModule e1
  v2 <- evaluateExp modifyModule e2
  t1 <- findType v1
  t2 <- findType v2
  case (t1, t2) of 
    (Just TBool, Just TBool) -> return $ expFromBool $ v1 == v2
    (Just (TUInt _), Just (TUInt _)) -> do
      return $ expFromBool $ v1 == v2
    _ -> error $ "Error in evaluateBoolIntBinOp: not matching types: " ++ (show v1) ++ " and " ++ (show v2)

evaluateBoolUnOp :: ModifyModuleType -> Trans -> (Bool -> Bool) -> Exp -> VerRes ([Trans], Exp)
evaluateBoolUnOp modifyModule op e = do
  v <- evaluateExp modifyModule e
  let bool = case v of
        ETrue -> True
        EFalse -> False
        _ -> error $ "Error in evaluateBoolUnOp: not a bool value: " ++ (show v)

  return $ expFromBool $ op bool

-}
