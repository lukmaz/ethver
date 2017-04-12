module DFSAuxEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import AbsEthver
import AuxPrismEthver
import AuxWorldPrismEthver
import CodePrismEthver
import ConstantsEthver
import WorldPrismEthver

-------------------
-- applyToTrList --
-------------------

applyToTrList :: ModifyModuleType -> (Trans -> VerRes [Trans]) -> [Trans] -> VerRes [Trans]
applyToTrList modifyModule fun trs = do
  foldM
    (\acc tr -> do
      newTrs <- fun tr
      return $ acc ++ newTrs
    )   
    []  
    trs 

-------------------------
-- deduction of values --
-------------------------

-- TODO: na pewno trzeba coś zrobić z updatesBranch
deduceVarValue :: Ident -> Trans -> Maybe Exp
deduceVarValue varIdent (trName, guards, updates) = 
  -- TODO: updates vs updatesBranch?
  deduceVarValueFromGuardsAndUpdatesBranch varIdent guards (head updates)

deduceVarValueFromGuardsAndUpdatesBranch :: Ident -> [Exp] -> [(Ident, Exp)] -> Maybe Exp
deduceVarValueFromGuardsAndUpdatesBranch varIdent guards updatesBranch =
  -- TODO: nested guards
  let
    filteredGuards = 
      filter
      (\x -> case x of
        Just _ -> True
        _ -> False
      )
      (map (valueFromCond varIdent) guards)
    filteredUpdates = filter (\(i, e) -> i == varIdent) updatesBranch
  in
    case filteredUpdates of
      ((var, value):t) -> Just value
      _ -> case filteredGuards of
        (h:t) -> h
        _ -> Nothing

deduceVarValueFromGuards :: Ident -> [Exp] -> Maybe Exp
deduceVarValueFromGuards varIdent guards = 
  let
    filteredGuards =
      filter
      (\x -> case x of
        Just _ -> True
        _ -> False
      )
      (map (valueFromCond varIdent) guards)
  in
    case filteredGuards of
      (h:t) -> h
      _ -> Nothing

-- TODO: Does not support bool operators different than And. (Needed?)
valueFromCond :: Ident -> Exp -> Maybe Exp
valueFromCond varName cond = 
  case cond of
    (EEq (EVar someVar) val) -> 
      if someVar == varName
        then Just val
        else Nothing
    (EAnd c1 c2) ->
      case ((valueFromCond varName c1), (valueFromCond varName c2)) of
        (Just val, _) -> Just val
        (_, Just val) -> Just val
        _ -> Nothing
    _ -> Nothing

-- TODO: Czy musi być deduceVarValueFromUpdate?

-- Aux: deduces value of a var from guards and updates
-- From updates first!



--  (createSmartOneTrans modifyModule (Fun funName args stms) condVarsList condArraysList) valuations

{-
addRandomUpdates :: ModifyModuleType -> [[(Ident, Exp)]] -> VerRes [[(Ident, Exp)]]
addRandomUpdates modifyModule oldUpdates = do
  world <- get
  let
    randomVarsList = Set.toList $ condRandoms world
    randomArraysList = arraysAsList $ condRandomArrays world

  case (randomVarsList, randomArraysList) of
    ([], []) -> return oldUpdates
    _ -> do
      types <- typesFromVarsAndArrays randomVarsList randomArraysList
      
      let
        maxVals = map maxRealValueOfType types
        valuations = generateAllVals maxVals

      randomArraysAsVars <- mapM (arrayToVar modifyModule) randomArraysList
      
      let 
        newUpdates = map
          (\vals -> (zip (randomVarsList ++ randomArraysAsVars) vals) ++ (head oldUpdates))
          valuations

      return newUpdates
-}


