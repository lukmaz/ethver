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

deduceVarValueFromGuards :: [Exp] -> Ident -> Maybe Exp
deduceVarValueFromGuards guards varName = 
  let
    filteredGuards =
      filter
      (\x -> case x of
        Just _ -> True
        _ -> False
      )
      (map (valueFromCond varName) guards)
  in
    case filteredGuards of
      (h:t) -> h
      _ -> Nothing

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
{-
deduceVarValue :: [Exp] -> [(Ident, Exp)] -> Ident -> Maybe Exp
deduceVarValue guards updatesBranch varName =
  -- TODO: nested guards
  let
    filteredGuards = 
      filter
      (\x -> case x of
        Just _ -> True
        _ -> False
      )
      (map (valueFromCond varName) guards)
    filteredUpdates = filter (\(i, e) -> i == varName) updatesBranch
  in
    case filteredUpdates of
      (h:t) -> Just h
      _ -> case filteredGuards of
        (h:t) -> Just h
        _ -> Nothing
-}

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


