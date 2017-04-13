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
-- determineExp --
------------------

-- used mainly for EArray: determineExp(tab[x]) = tab_2 for x = 2
-- uses x value from guards

determineExp :: Exp -> Trans -> Exp

determineExp (EOr e1 e2) tr = EOr (determineExp e1 tr) (determineExp e2 tr)
determineExp (EAnd e1 e2) tr = EAnd (determineExp e1 tr) (determineExp e2 tr)
determineExp (EEq e1 e2) tr = EEq (determineExp e1 tr) (determineExp e2 tr)
determineExp (ENe e1 e2) tr = ENe (determineExp e1 tr) (determineExp e2 tr)
determineExp (ELt e1 e2) tr = ELt (determineExp e1 tr) (determineExp e2 tr)
determineExp (ELe e1 e2) tr = ELe (determineExp e1 tr) (determineExp e2 tr)
determineExp (EGt e1 e2) tr = EGt (determineExp e1 tr) (determineExp e2 tr)
determineExp (EGe e1 e2) tr = EGe (determineExp e1 tr) (determineExp e2 tr)
determineExp (EAdd e1 e2) tr = EAdd (determineExp e1 tr) (determineExp e2 tr)
determineExp (ESub e1 e2) tr = ESub (determineExp e1 tr) (determineExp e2 tr)
determineExp (EMul e1 e2) tr = EMul (determineExp e1 tr) (determineExp e2 tr)
determineExp (EDiv e1 e2) tr = EDiv (determineExp e1 tr) (determineExp e2 tr)
determineExp (EMod e1 e2) tr = EMod (determineExp e1 tr) (determineExp e2 tr)

determineExp (ENeg e) tr = ENeg (determineExp e tr)
determineExp (ENot e) tr = ENot (determineExp e tr)

determineExp (EArray (Ident arrName) index) tr = 
  case index of
    EInt x ->
      EVar $ Ident $ arrName ++ "_" ++ (show x)
    EVar varIdent -> do 
      case deduceVarValue varIdent tr of
        (Just (EInt x)) ->
          EVar $ Ident $ arrName ++ "_" ++ (show x)
        Nothing -> 
          error $ "Array index cannot be determined from guards. Array: " ++ (show $ EArray (Ident arrName) index)
            ++ "\nTrans: " ++ (show tr)
    _ -> 
      error $ "Array index different than ESender, EInt a, or EVar a"

determineExp (EInt x) _ = EInt x

determineExp (EVar varIdent) tr = 
  case deduceVarValue varIdent tr of
    (Just (EInt x)) ->
      EInt x
    Nothing ->
      EVar varIdent
      -- chyba musi tak być, bo jak inaczej sobie poradzić z wartością argumentu funkcji?
      --error $ "Value of variable " ++ (show varIdent) ++ " not determined from guards: " ++ (show guards)

determineExp exp _ = 
  error $ "This type of expression not supported by determineExp: " ++ (show exp)

-----------------
-- evaluateExp --
-----------------

evaluateExp :: ModifyModuleType -> Exp -> Trans -> VerRes [Trans]

evaluateExp modifyModule (EOr e1 e2) tr = evaluateExp2Arg modifyModule e1 e2 tr
evaluateExp modifyModule (EAnd e1 e2) tr = evaluateExp2Arg modifyModule e1 e2 tr
evaluateExp modifyModule (EEq e1 e2) tr = evaluateExp2Arg modifyModule e1 e2 tr
evaluateExp modifyModule (ENe e1 e2) tr = evaluateExp2Arg modifyModule e1 e2 tr
evaluateExp modifyModule (ELt e1 e2) tr = evaluateExp2Arg modifyModule e1 e2 tr
evaluateExp modifyModule (ELe e1 e2) tr = evaluateExp2Arg modifyModule e1 e2 tr
evaluateExp modifyModule (EGt e1 e2) tr = evaluateExp2Arg modifyModule e1 e2 tr
evaluateExp modifyModule (EGe e1 e2) tr = evaluateExp2Arg modifyModule e1 e2 tr
evaluateExp modifyModule (EAdd e1 e2) tr = evaluateExp2Arg modifyModule e1 e2 tr
evaluateExp modifyModule (ESub e1 e2) tr = evaluateExp2Arg modifyModule e1 e2 tr
evaluateExp modifyModule (EMul e1 e2) tr = evaluateExp2Arg modifyModule e1 e2 tr
evaluateExp modifyModule (EDiv e1 e2) tr = evaluateExp2Arg modifyModule e1 e2 tr
evaluateExp modifyModule (EMod e1 e2) tr = evaluateExp2Arg modifyModule e1 e2 tr

evaluateExp modifyModule (ENeg e) tr = evaluateExp modifyModule e tr
evaluateExp modifyModule (ENot e) tr = evaluateExp modifyModule e tr

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
      case deduceVarValue varIdent (trName, guards, updates) of
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
  case deduceVarValue varIdent (trName, guards, updates) of
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

evaluateExp2Arg :: ModifyModuleType -> Exp -> Exp -> Trans -> VerRes [Trans]
evaluateExp2Arg modifyModule exp1 exp2 tr = do
  evaluateExp modifyModule exp1 tr >>= applyToTrList (evaluateExp modifyModule exp2)
