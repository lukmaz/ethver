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

applyToTrList :: (Trans -> VerRes [Trans]) -> [Trans] -> VerRes [Trans]
applyToTrList fun trs = do
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

deduceVarValue :: Ident -> [Exp] -> [(Ident, Exp)] -> Maybe Exp
deduceVarValue varIdent guards updatesBranch = 
  case deduceVarValueFromUpdatesBranch varIdent updatesBranch of
    Just val -> Just val
    _ -> case deduceVarValueFromGuards varIdent guards of
      Just val -> Just val
      _ -> Nothing

deduceVarValueFromUpdatesBranch :: Ident -> [(Ident, Exp)] -> Maybe Exp
deduceVarValueFromUpdatesBranch varIdent updatesBranch =
  let
    filteredUpdates = filter (\(i, _) -> i == varIdent) updatesBranch
  in
    case filteredUpdates of
      ((_, value):t) -> Just value
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

-- TODO: Assumption: only Eq guards
-- TODO: Does not support bool operators different than And. (Needed?)
valueFromCond :: Ident -> Exp -> Maybe Exp
valueFromCond varIdent cond = 
  case cond of
    (EEq (EVar someVar) val) -> 
      if someVar == varIdent
        then Just val
        else Nothing
    (EEq val (EVar someVar)) ->
      if someVar == varIdent
        then Just val
        else Nothing
    (EAnd c1 c2) ->
      case ((valueFromCond varIdent c1), (valueFromCond varIdent c2)) of
        (Just val, _) -> Just val
        (_, Just val) -> Just val
        _ -> Nothing
    _ -> Nothing

--------------------------------------------------------
-- applyCond -------------------------------------------
-- applies cond to a Trans. ----------------------------
-- Can create empty list of Transs (if contradiction) --
-- or longer list (if cond is an alternative) ----------
--------------------------------------------------------

{-
verDFSIf :: ModifyModule -> Exp -> Stm -> Trans -> VerRes [Trans]
verDFSIf modifyModule (EEq (EVar varIdent) value) ifBlock tr@(trName, guards, updates) = do
  let 
    determinedCond = determineExp cond tr
    deducedFromBranches = map (deduceVarValueFromUpdatesBranch varIdent) updates
    determined = not $ elem Nothing deducedFromBranches

  if determined
-}  

applyCondToBranch :: Exp -> [(Ident, Exp)] -> [(Ident, Exp)]
applyCondToBranchWithPos :: Exp -> [(Ident, Exp)] -> [(Ident, Exp)]
applyCondToBranchWithNeg :: Exp -> [(Ident, Exp)] -> [(Ident, Exp)]

--TODO
applyCondToBranch _ branch = branch
applyCondToBranchWithPos _ branch = branch
applyCondToBranchWithNeg _ branch = branch
{-
applyCondToBranch (EEq (EVar varIdent) value) branch =
  case deduceVarValueFromUpdatesBranch varIdent branch of
    Just oldValue ->
      if (oldValue == value)




        then return branch
      
      
      
      else return []
    Nothing ->
      return [(trName, (EEq (EVar varIdent) value):guards, updates)]
-}

applyCond :: Exp -> Trans -> VerRes [Trans]

applyCond (EEq (EVar varIdent) value) (trName, guards, updates) = do
  let 
    deducedFromBranches = map (deduceVarValueFromUpdatesBranch varIdent) updates
    determined = not $ elem Nothing deducedFromBranches

  if determined
    then do
      let newUpdates = map (applyCondToBranch (EEq (EVar varIdent) value)) updates
      return [(trName, guards, newUpdates)]
    else
      case deduceVarValueFromGuards varIdent guards of
        Just oldValue ->
          if (oldValue == value)
            then do
              let newUpdates = map (applyCondToBranchWithPos (EEq (EVar varIdent) value)) updates
              return [(trName, guards, newUpdates)]
            else do
              let newUpdates = map (applyCondToBranchWithNeg (EEq (EVar varIdent) value)) updates
              return [(trName, guards, newUpdates)]
        Nothing -> do
          let newUpdatesPos = map (applyCondToBranchWithPos (EEq (EVar varIdent) value)) updates
          let newUpdatesNeg = map (applyCondToBranchWithNeg (EEq (EVar varIdent) value)) updates
          return [(trName, (EEq (EVar varIdent) value):guards, newUpdatesPos),
            (trName, (ENe (EVar varIdent) value):guards, newUpdatesNeg)]


applyCond (EEq value (EVar varIdent)) tr =
  applyCond (EEq (EVar varIdent) value) tr

applyCond (ENe (EVar varIdent) value) (trName, guards, updates) = do
  case deduceVarValue varIdent updates of
    Just oldValue ->
      if (oldValue == value)
        then return []
        else return [(trName, guards, updates)]
    Nothing ->
      return [(trName, (ENe (EVar varIdent) value):guards, updates)]
  
applyCond (ENe value (EVar varIdent)) tr =
  applyCond (ENe (EVar varIdent) value) tr

applyCond (EAnd cond1 cond2) tr = do
  applyCond cond1 tr >>= applyToTrList (applyCond cond2)

applyCond (EOr cond1 cond2) tr = do
  tr1 <- applyCond cond1 tr
  tr2 <- applyCond cond2 tr
  return $ tr1 ++ tr2

applyCond cond _ = do
  error $ "This type of condition not supported by applyCond: " ++ (show cond)

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


