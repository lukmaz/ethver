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

-- TODO: multi-branch updates
deduceVarValueFromBranch :: Ident -> Branch -> Maybe Exp
deduceVarValueFromBranch varIdent (Alive updatesBranch) =
  let
    filteredUpdates = filter (\(i, _) -> i == varIdent) updatesBranch
  in
    case filteredUpdates of
      ((_, value):t) -> Just value
      _ -> Nothing

--TODO: Alive?
deduceVarValueFromBranch varIdent (Dead updatesBranch) =
  deduceVarValueFromBranch varIdent (Alive updatesBranch) 

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
-- of longer list (if cond is an alternative) ----------
--------------------------------------------------------

applyCond :: Exp -> Trans -> VerRes [Trans]

-- TODO
{-
applyCond (EEq (EInt x) (EInt y)) tr@(trName, guards, updates) = do
  if (x == y)
    then return [tr]
    else return []

-- TODO
applyCond (ENe (EInt x) (EInt y)) tr@(trName, guards, updates) = do
  if (x /= y)
    then return [tr]
    else return []
-}

-- NOWE
applyCond (EEq (EVar varIdent) value) (trName, guards, updates) = do
  let deducedValues = map (deduceVarValueFromBranch varIdent) updates
  if not $ elem Nothing deducedValues
    -- value of varIdent determined in every branch
    then
      let 
        branches = map (applyCondToBranch True (EEq (EVar varIdent) value)) $ zip updates deducedValues
      in
        return [(trName, guards, branches)]
    -- value of varIdent not always determined
    else
      let 
        ifGuards = applyCondToGuards (EEq (EVar varIdent) value) guards
        elseGuards = applyCondToGuards (ENe (EVar varIdent) value) guards
        ifBranches = map (applyCondToBranch True (EEq (EVar varIdent) value)) $ zip updates deducedValues
        elseBranches = map (applyCondToBranch False (EEq (EVar varIdent) value)) $ zip updates deducedValues
      in
        return [(trName, ifGuards, ifBranches), (trName, elseGuards, elseBranches)]

applyCond (ENe (EVar varIdent) value) (trName, guards, updates) = do
  let deducedValues = map (deduceVarValueFromBranch varIdent) updates
  if not $ elem Nothing deducedValues
    -- value of varIdent determined in every branch
    then
      let 
        branches = map (applyCondToBranch True (ENe (EVar varIdent) value)) $ zip updates deducedValues
      in
        return [(trName, guards, branches)]
    -- value of varIdent not always determined
    else
      let 
        ifGuards = applyCondToGuards (ENe (EVar varIdent) value) guards
        elseGuards = applyCondToGuards (EEq (EVar varIdent) value) guards
        ifBranches = map (applyCondToBranch True (ENe (EVar varIdent) value)) $ zip updates deducedValues
        elseBranches = map (applyCondToBranch False (ENe (EVar varIdent) value)) $ zip updates deducedValues
      in
        return [(trName, ifGuards, ifBranches), (trName, elseGuards, elseBranches)]

applyCond (EEq value (EVar varIdent)) tr =
  applyCond (EEq (EVar varIdent) value) tr

applyCond (ENe value (EVar varIdent)) tr =
  applyCond (ENe (EVar varIdent) value) tr

--TODO
{-
applyCond (EAnd cond1 cond2) tr = do
  applyCond cond1 tr >>= applyToTrList (applyCond cond2)

applyCond (EOr cond1 cond2) tr = do
  tr1 <- applyCond cond1 tr
  tr2 <- applyCond cond2 tr
  return $ tr1 ++ tr2
-}

applyCond cond _ = do
  error $ "This type of condition not supported by applyCond: " ++ (show cond)


-- applyCondToBranch

applyCondToBranch :: Bool -> Exp -> (Branch, Maybe Exp) -> Branch

applyCondToBranch ifCase (EEq (EVar varIdent) value) (branch, deducedVal) =
  case deducedVal of
    Just v ->
      if (v == value)
        then branch
        else makeDead branch
    Nothing ->
      if ifCase
        then branch
        else makeDead branch

applyCondToBranch ifCase (ENe (EVar varIdent) value) (branch, deducedVal) =
  case deducedVal of
    Just v ->
      if (v /= value)
        then branch
        else makeDead branch
    Nothing ->
      if ifCase
        then branch
        else makeDead branch


-- applyCondToGuards
-- TODO: da sie zoptymalizowac?

applyCondToGuards :: Exp -> [Exp] -> [Exp]
applyCondToGuards cond guards = cond:guards

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

makeAlive :: Branch -> Branch
makeAlive (Alive x) = Alive x
makeAlive (Dead x) = Alive x

makeDead :: Branch -> Branch
makeDead (Alive x) = Dead x
makeDead (Dead x) = Dead x
