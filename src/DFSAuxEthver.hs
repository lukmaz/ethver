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


---
-- TODO: TU TEZ MOZNA WYWALIC VerRes?
---


-----------------
-- applyToList --
-----------------

applyToList :: (a -> VerRes [b]) -> [a] -> VerRes [b]
applyToList fun trs = do
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
deduceVarValueFromBranch varIdent (updatesBranch, _) =
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
-- of longer list (if cond is an alternative) ----------
--------------------------------------------------------

applyCond :: Exp -> Trans -> VerRes [Trans]

-- EEq and ENe between EVar and anything

applyCond (EEq (EVar varIdent) value) tr =
  applyEqOrNeCond (EEq (EVar varIdent) value) tr

applyCond (ENe (EVar varIdent) value) tr =
  applyEqOrNeCond (ENe (EVar varIdent) value) tr

-- EEq and ENe between ESender and anything

applyCond (EEq ESender value) tr =
  applySenderEqOrNeCond (EEq ESender value) tr

applyCond (ENe ESender value) tr =
  applySenderEqOrNeCond (ENe ESender value) tr


-- EAnd, EOr

applyCond (EAnd cond1 cond2) tr = do
  applyCond (makeLeft cond1) tr >>= applyToList (applyCond (makeLeft cond2))

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
    -- assumption: branches can differ only by the head of their liveness
    makeDeadIfBothDead :: (Branch, Branch) -> Branch
    makeDeadIfBothDead ((br1, liv1h:liv1t), (br2, liv2h:liv2t)) =
      if ((liv1h == Dead) && (liv2h == Dead))
        then (br1, Dead:liv1t)
        else (br1, Alive:liv1t)

    varIdent1 = identFromComp cond1
    varIdent2 = identFromComp cond2
    deducedValues1 = map (deduceVarValueFromBranch varIdent1) updates
    deducedValues2 = map (deduceVarValueFromBranch varIdent2) updates
    
    posPosGuards = applyCondToGuards cond1 $ applyCondToGuards cond2 guards
    negPosGuards = applyCondToGuards (negateExp cond1) $ applyCondToGuards cond2 guards
    posNegGuards = applyCondToGuards cond1 $ applyCondToGuards (negateExp cond2) guards
    
    posPosBranches1 = map (applyCondToBranch True cond1) $ zip updates deducedValues1
    posPosBranches2 = map (applyCondToBranch True cond2) $ zip updates deducedValues2
    posPosBranches = map makeDeadIfBothDead $ zip posPosBranches1 posPosBranches2

    negPosBranches1 = map (applyCondToBranch False cond1) $ zip updates deducedValues1
    negPosBranches2 = map (applyCondToBranch True cond2) $ zip updates deducedValues2
    negPosBranches = map makeDeadIfBothDead $ zip negPosBranches1 negPosBranches2

    posNegBranches1 = map (applyCondToBranch True cond1) $ zip updates deducedValues1
    posNegBranches2 = map (applyCondToBranch False cond2) $ zip updates deducedValues2
    posNegBranches = map makeDeadIfBothDead $ zip posNegBranches1 posNegBranches2
      
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

-- applySenderEqOrNeCond
applySenderEqOrNeCond :: Exp -> Trans -> VerRes [Trans]
applySenderEqOrNeCond cond (trName, guards, updates) =
  let
    ifGuards = applyCondToGuards cond guards
    elseGuards = applyCondToGuards (negateExp cond) guards
    ifBranches = map (\(br, liv) -> (br, (head liv):liv)) updates
    elseBranches = map (\(br, liv) -> (br, Dead:liv)) updates
  in
    return [(trName, ifGuards, ifBranches), (trName, elseGuards, elseBranches)]

-- applyCondToBranch

applyCondToBranch :: Bool -> Exp -> (Branch, Maybe Exp) -> Branch

applyCondToBranch ifCase (EEq (EVar varIdent) value) ((br, liv), deducedVal) =
  case deducedVal of
    Just v ->
      if (v == value)
        then (br, (head liv):liv)
        else (br, Dead:liv)
    Nothing ->
      if ifCase
        then (br, (head liv):liv)
        else (br, Dead:liv)

applyCondToBranch ifCase (ENe (EVar varIdent) value) ((br, liv), deducedVal) =
  case deducedVal of
    Just v ->
      if (v /= value)
        then (br, (head liv):liv)
        else (br, Dead:liv)
    Nothing ->
      if ifCase
        then (br, (head liv):liv)
        else (br, Dead:liv)


-- applyCondToGuards
-- TODO: da sie zoptymalizowac?

applyCondToGuards :: Exp -> [Exp] -> [Exp]
applyCondToGuards cond guards = cond:guards

---------------
-- transfers --
---------------

dfsTransferFromContract :: Ident -> Exp -> Trans -> VerRes [Trans]
dfsTransferFromContract receiverAddress amount tr =
  dfsTransferMoney iContractBalance receiverAddress (EVar iMaxUserBalance) amount tr

dfsTransferMoney :: Ident -> Ident -> Exp -> Exp -> Trans -> VerRes [Trans]
dfsTransferMoney from to maxTo amount tr@(trName, guards, updates) = do
  let 
    newGuards1 = applyCondToGuards (EGe (EVar from) amount) guards
    newGuards2 = applyCondToGuards (ELe (EAdd (EVar to) amount) maxTo) newGuards1
  -- TODO: czy wystarczy addSimpleAssesToTr? (cf. zalozenia przed def. f. addSimple...)
    updates1 = addAssToUpdates from (ESub (EVar from) amount) updates
    updates2 = addAssToUpdates to (EAdd (EVar to) amount) updates1
  return [(trName, newGuards2, updates2)]

---------
-- Ass --
---------
-- adds an assignment to a single transition
-- male TODO: to jest sztuczne, że zwraca [Trans], a nie Trans
addAssToTr :: Ident -> Exp -> Trans -> VerRes [Trans]

addAssToTr varIdent value (trName, guards, updates) = do
  case value of
    ERand (EInt range) ->
      let newUpdates = addRandomAssToUpdates varIdent range updates
      in return [(trName, guards, newUpdates)]
    _ ->
      let newUpdates = addAssToUpdates varIdent value updates
      in return [(trName, guards, newUpdates)]

-- adds a non-random assignment to updates
addAssToUpdates :: Ident -> Exp -> [Branch] -> [Branch]
addAssToUpdates varIdent value updates = do
  foldl
    (\acc branch ->
      let partialBranch = addAssToUpdatesBranch varIdent value branch
      in partialBranch:acc
    )
    []
    updates

-- adds a random assignment to updates
addRandomAssToUpdates :: Ident -> Integer -> [Branch] -> [Branch]
addRandomAssToUpdates varIdent range updates =
  foldl
    (\acc val ->
      let partialBranches = addAssToUpdates varIdent (EInt val) updates
      in partialBranches ++ acc
    )
    []
    [0..(range - 1)]

-- adds a particular assignment to an updates branch
addAssToUpdatesBranch :: Ident -> Exp -> Branch -> Branch
addAssToUpdatesBranch varIdent value (br, Dead:t) =
  (br, Dead:t)

addAssToUpdatesBranch varIdent value (br, Alive:t) =
  let
    deleteOld :: [(Ident, Exp)] -> [(Ident, Exp)]
    deleteOld list = filter
      (\(i, _) -> i /= varIdent)
      list
    newBranch old = (varIdent, value):(deleteOld old)
  in
    applyToBranch newBranch (br, Alive:t)


