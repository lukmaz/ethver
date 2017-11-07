module DFSPrismEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import AbsEthver
import AuxPrismEthver
import AuxWorldPrismEthver
import CodePrismEthver
import ConstantsEthver
import DFSAuxEthver
import DFSEvalEthver
import WorldPrismEthver

---------------
-- verDFSFun --
---------------

-- for a given function creates a command for every important valuation
verDFSFun :: ModifyModuleType -> Function -> VerRes ()
verDFSFun modifyModule (Fun funName args stms) = do
  mod <- modifyModule id
  let
    stVar = Ident $ stateVar mod
    initGuards = [EEq (EVar stVar) (EInt $ currState mod)]
    --TODO: Alive?
    initUpdates = [([(stVar, EInt 1)], [Alive])]
  trs <- verDFSStm modifyModule (SBlock stms) [("", initGuards, initUpdates)]
  mapM_
    (\tr -> modifyModule (\mod -> mod {transs = tr:(transs mod)}))
    trs

---------------
-- verDFSStm --
---------------


-------------
-- TODO: Tu VerRes musi zostać, zeby dedukować typ zmiennej
-------------

verDFSStm :: ModifyModuleType -> Stm -> [Trans] -> VerRes ([Trans])

verDFSStm modifyModule (SBlock []) trs = do
  return trs

verDFSStm modifyModule (SBlock (stmH:stmT)) trs = do
  verDFSStm modifyModule stmH trs >>= 
    verDFSStm modifyModule (SBlock stmT)

----

---------------------------------------------
-- TODO OOOOOOOOOOOOOOOOOOOOOO (dlaczego?) --
---------------------------------------------

----

-- For a moment it returns only single Trans (and works for only simple ass)

verDFSStm modifyModule (SAss varIdent value) oldTrs = do
  newTrsAndVals <- applyToList (evaluateArray value) oldTrs
  applyToList 
    (\(tr, vals) -> return [addSimpleAssesToTr 
      (map 
        (\val -> (varIdent, val))
        vals
      ) 
      tr]
    )
    newTrsAndVals

verDFSStm modifyModule (SArrAss arrIdent index value) oldTrs = do
  -- TODO: evaluateExp?
  --newTrs <- applyToList (evaluateExp modifyModule index) oldTrs >>= 
  --  applyToList (evaluateExp modifyModule value)
  applyToList (addArrAssToTr arrIdent index value) oldTrs

verDFSStm modifyModule (SIf cond ifBlock) trs = do
  -- TODO: evaluateExp?
  --condTranss <- applyToList (evaluateExp modifyModule cond) trs
  applyToList (verDFSIf modifyModule cond ifBlock) trs

verDFSStm modifyModule (SIfElse cond ifBlock elseBlock) trs = do
  -- TODO: evaluateExp?
  --condTranss <- applyToList (evaluateExp modifyModule cond) trs
  applyToList (verDFSIfElse modifyModule cond ifBlock elseBlock) trs

verDFSStm modifyModule (SWhile _ _) _ = do
  error $ "while loop not supported in verDFS"

  
---------
-- Ass --
---------

-- TODO: Nie wiem, czy problemu z wieloma transami nie rozwiaze poziom wyzej
-- W zwiazku z tym na tym poziomie robilbym tylko addAssToBranch

-- given a list of assignment of the same size as number of branches in trans
-- adds the assignments to the corresponding branches

-- TODO:
--addAssesToTr :: [(Ident, Exp)] -> Trans -> VerRes [Trans]


-- adds a list of assignments to a Trans
-- Assumption 1: #list = #branches in Trans
-- Assumption 2: simple asses <=> no need for multi-branches/multi-transes
addSimpleAssesToTr :: [(Ident, Exp)] -> Trans -> Trans
addSimpleAssesToTr asses tr@(trName, guards, updates) = 
  (trName, guards, map
    (\((varName, value), branch) -> addAssToUpdatesBranch varName value branch)
    (zip asses updates)
  )

-- TODO: TO JEST CHYBA DO WYWALENIA
-------------------------------------

-- Bo moze byc inny ass w kazdym branchu. Zamiast tego addAssesToTr

-- adds an assignment to a single transition
-- assumes value is evaluated
-- male TODO: to jest sztuczne, że zwraca [Trans], a nie Trans
addAssToTr :: Ident -> Exp -> Trans -> VerRes [Trans]

addAssToTr varIdent value (trName, guards, updates) = do
  --TODO: determineExp?
  --let determinedValue = determineExp value (trName, guards, updates)
  case value of
    ERand (EInt range) ->
      let newUpdates = addRandomAssToUpdates varIdent range updates
      in return [(trName, guards, newUpdates)]
    _ -> 
      let newUpdates = addAssToUpdates varIdent value updates
      in return [(trName, guards, newUpdates)]

-----------------
-- TODO: TO CHYBA TEZ DO WYWALENIA:
-------------------------------


-- TODO: To, żeby działało, musi być jakieś determineExp. Ale nie może być z Tr.
-- Pewnie "addArrAssToBranch"?
-- simlarly, assumes index and value are evaluated
addArrAssToTr :: Ident -> Exp -> Exp -> Trans -> VerRes [Trans]
addArrAssToTr arrIdent index value tr = do
  error $ "addArrAssToTr: Arrays not supported.\n"
  -- TODO: determineExp?
  --case determineExp (EArray arrIdent index) tr of
  -- Linijka poniżej jest oczywiście bez sensu.
  {-case (EArray arrIdent index) of
    EVar varIdent ->
      addAssToTr varIdent value tr
    _ ->
      error $ "Cannot determine var name from array name after evaluation: " ++ (show $ EArray arrIdent index)
  -}

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

--------
-- If --
--------

-- verDFSIf
verDFSIf :: ModifyModuleType -> Exp -> Stm -> Trans -> VerRes [Trans]
verDFSIf modifyModule cond ifBlock tr@(trName, guards, updates) = do
  afterCondTranss <- applyCond (makeLeft cond) (trName, guards, updates)
  afterBlockTranss <- verDFSStm modifyModule ifBlock afterCondTranss
  
  return $ map
    (\(trName, guards, updates) -> (trName, guards, map removeHeadLiv updates))
    afterBlockTranss
      where
        removeHeadLiv :: Branch -> Branch
        removeHeadLiv (br, liv) = (br, tail liv)

verDFSIfElse :: ModifyModuleType -> Exp -> Stm -> Stm -> Trans -> VerRes [Trans]
verDFSIfElse modifyModule cond ifBlock elseBlock tr = do
  error $ "verDFSIfElse not implemented"
  -- TODO

  {-
  STARE:
  posCondTranss <- applyCond cond tr
  posTranss <- verDFSStm modifyModule ifBlock posCondTranss

  negCondTranss <- applyCond (negateExp cond) tr
  negTranss <- verDFSStm modifyModule elseBlock negCondTranss

  return $ posTranss ++ negTranss
  -}

