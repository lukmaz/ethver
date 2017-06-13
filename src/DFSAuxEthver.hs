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

applyCond (EEq (EVar varIdent) value) tr =
  applyEqOrNeCond (EEq (EVar varIdent) value) tr

applyCond (ENe (EVar varIdent) value) tr =
  applyEqOrNeCond (ENe (EVar varIdent) value) tr

applyCond (EEq value (EVar varIdent)) tr =
  applyCond (EEq (EVar varIdent) value) tr

applyCond (ENe value (EVar varIdent)) tr =
  applyCond (ENe (EVar varIdent) value) tr

applyCond (EAnd cond1 cond2) tr = do
  applyCond cond1 tr >>= applyToTrList (applyCond cond2)

applyCond (EOr cond1 cond2) tr = do
  if (isLeftComp $ makeLeft cond1) && (isLeftComp $ makeLeft cond2)
    then
      applyOrCond (makeLeft cond1) (makeLeft cond2) tr
    else
      error $ "This type of alternative not supported in applyCond: " ++ (show (EOr cond1 cond2))

applyCond (ENot (EEq e1 e2)) tr = 
  applyCond (ENe e1 e2) tr

applyCond (ENot (ENe e1 e2)) tr = 
  applyCond (EEq e1 e2) tr

applyCond cond _ = do
  error $ "This type of condition not supported by applyCond: " ++ (show cond)


-- applyOrCond

applyOrCond :: Exp -> Exp -> Trans -> VerRes [Trans]
applyOrCond cond1 cond2 (trName, guards, updates) = do
  let 
    deadIfBothDead :: (Branch, Branch) -> Branch
    deadIfBothDead (branch1, branch2) =
      case (branch1, branch2) of
        (Dead b1, Dead b2) -> Dead b1
        (Alive b1, _) -> Alive b1
        (_, Alive b2) -> Alive b2

    varIdent1 = identFromComp cond1
    varIdent2 = identFromComp cond2
    deducedValues1 = map (deduceVarValueFromBranch varIdent1) updates
    deducedValues2 = map (deduceVarValueFromBranch varIdent2) updates
    
    posPosGuards = applyCondToGuards cond1 $ applyCondToGuards cond2 guards
    negPosGuards = applyCondToGuards (negateExp cond1) $ applyCondToGuards cond2 guards
    posNegGuards = applyCondToGuards cond1 $ applyCondToGuards (negateExp cond2) guards
    
    posPosBranches1 = map (applyCondToBranch True cond1) $ zip updates deducedValues1
    posPosBranches2 = map (applyCondToBranch True cond2) $ zip updates deducedValues2
    posPosBranches = map deadIfBothDead $ zip posPosBranches1 posPosBranches2

    negPosBranches1 = map (applyCondToBranch False cond1) $ zip updates deducedValues1
    negPosBranches2 = map (applyCondToBranch True cond2) $ zip updates deducedValues2
    negPosBranches = map deadIfBothDead $ zip negPosBranches1 negPosBranches2

    posNegBranches1 = map (applyCondToBranch True cond1) $ zip updates deducedValues1
    posNegBranches2 = map (applyCondToBranch False cond2) $ zip updates deducedValues2
    posNegBranches = map deadIfBothDead $ zip posNegBranches1 posNegBranches2
      
  return [(trName, posPosGuards, posPosBranches), (trName, negPosGuards, negPosBranches),
    (trName, posNegGuards, posNegBranches)]

-- applyEqOrNeCond

applyEqOrNeCond :: Exp -> Trans -> VerRes [Trans]
applyEqOrNeCond cond (trName, guards, updates) = do
  let 
    varIdent = identFromComp cond
    deducedValues = map (deduceVarValueFromBranch varIdent) updates
  if not $ elem Nothing deducedValues
    -- value of varIdent determined in every branch
    then
      let 
        branches = map (applyCondToBranch True cond) $ zip updates deducedValues
      in
        return [(trName, guards, branches)]
    -- value of varIdent not always determined
    else
      let 
        ifGuards = applyCondToGuards cond guards
        elseGuards = applyCondToGuards (negateExp cond) guards
        ifBranches = map (applyCondToBranch True cond) $ zip updates deducedValues
        elseBranches = map (applyCondToBranch False cond) $ zip updates deducedValues
      in
        return [(trName, ifGuards, ifBranches), (trName, elseGuards, elseBranches)]


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
