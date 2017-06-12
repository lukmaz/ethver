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
    initUpdates = [Alive [(stVar, EInt 1)]]
  trs <- verDFSStm modifyModule (SBlock stms) [("", initGuards, initUpdates)]
  mapM_
    (\tr -> modifyModule (\mod -> mod {transs = tr:(transs mod)}))
    trs

---------------
-- verDFSStm --
---------------

verDFSStm :: ModifyModuleType -> Stm -> [Trans] -> VerRes ([Trans])

verDFSStm modifyModule (SBlock []) trs = do
  return trs

verDFSStm modifyModule (SBlock (stmH:stmT)) trs = do
  verDFSStm modifyModule stmH trs >>= 
    verDFSStm modifyModule (SBlock stmT)

verDFSStm modifyModule (SAss varIdent value) oldTrs = do
  -- TODO: evaluateExp?
  --newTrs <- applyToTrList (evaluateExp modifyModule value) oldTrs
  applyToTrList (addAssToTr varIdent value) oldTrs

verDFSStm modifyModule (SArrAss arrIdent index value) oldTrs = do
  -- TODO: evaluateExp?
  --newTrs <- applyToTrList (evaluateExp modifyModule index) oldTrs >>= 
  --  applyToTrList (evaluateExp modifyModule value)
  applyToTrList (addArrAssToTr arrIdent index value) oldTrs

verDFSStm modifyModule (SIf cond ifBlock) trs = do
  -- TODO: evaluateExp?
  --condTranss <- applyToTrList (evaluateExp modifyModule cond) trs
  applyToTrList (verDFSIf modifyModule cond ifBlock) trs

verDFSStm modifyModule (SIfElse cond ifBlock elseBlock) trs = do
  -- TODO: evaluateExp?
  --condTranss <- applyToTrList (evaluateExp modifyModule cond) trs
  applyToTrList (verDFSIfElse modifyModule cond ifBlock elseBlock) trs

verDFSStm modifyModule (SWhile _ _) _ = do
  error $ "while loop not supported in verDFS"

  
---------
-- Ass --
---------

-- adds an assignment to a single transition
-- assumes value is evaluated
-- male TODO: to jest sztuczne, że zwraca [Trans], a nie Trans
addAssToTr :: Ident -> Exp -> Trans -> VerRes [Trans]

addAssToTr varIdent value (trName, guards, updates) = do
  --TODO: determineExp?
  --let determinedValue = determineExp value (trName, guards, updates)
  case value of
    ERand (EInt range) -> do
      newUpdates <- addRandomAssToUpdates varIdent range updates
      return [(trName, guards, newUpdates)]
    _ -> do
      newUpdates <- addAssToUpdates varIdent value updates
      return [(trName, guards, newUpdates)]

-- TODO: To, żeby działało, musi być jakieś determineExp. Ale nie może być z Tr.
-- Pewnie "addArrAssToBranch"?
-- simlarly, assumes index and value are evaluated
addArrAssToTr :: Ident -> Exp -> Exp -> Trans -> VerRes [Trans]
addArrAssToTr arrIdent index value tr = do
  -- TODO: determineExp?
  --case determineExp (EArray arrIdent index) tr of
  -- Linijka poniżej jest oczywiście bez sensu.
  case (EArray arrIdent index) of
    EVar varIdent ->
      addAssToTr varIdent value tr
    _ ->
      error $ "Cannot determine var name from array name after evaluation: " ++ (show $ EArray arrIdent index)

-- adds a non-random assignment to updates
addAssToUpdates :: Ident -> Exp -> [Branch] -> VerRes [Branch]
addAssToUpdates varIdent value updates = do
  foldM
    (\acc branch -> do
      partialBranch <- addAssToUpdatesBranch varIdent value branch
      return $ partialBranch:acc
    )
    []
    updates

-- adds a random assignment to updates
addRandomAssToUpdates :: Ident -> Integer -> [Branch] -> VerRes [Branch]
addRandomAssToUpdates varIdent range updates = do
  foldM
    (\acc val -> do
      partialBranches <- addAssToUpdates varIdent (EInt val) updates
      return $ partialBranches ++ acc
    )
    []
    [0..(range - 1)]

-- adds a particular assignment to an updates branch
addAssToUpdatesBranch :: Ident -> Exp -> Branch -> VerRes Branch
addAssToUpdatesBranch varIdent value (Dead branch) = 
  return (Dead branch)

addAssToUpdatesBranch varIdent value (Alive branch) = 
  let 
    deleteOld :: [(Ident, Exp)] -> [(Ident, Exp)]
    deleteOld list = filter
      (\(i, _) -> i /= varIdent)
      list
    newBranch old = (varIdent, value):(deleteOld old)
  in
    return $ applyToBranch newBranch (Alive branch)

--------
-- If --
--------

-- verDFSIf
verDFSIf :: ModifyModuleType -> Exp -> Stm -> Trans -> VerRes [Trans]
verDFSIf modifyModule cond ifBlock tr@(trName, guards, updates) = do
  let 
    --TODO: determineExp?
    --determinedCond = determineExp cond tr

    -- TODO: chyba trzeba robić zagnieżdżanie makeAlive na wypadek zagnieżdżonych ifów
    aliveUpdates = map makeAlive updates

  afterCondTranss <- applyCond cond (trName, guards, aliveUpdates)
  afterBlockTranss <- verDFSStm modifyModule ifBlock afterCondTranss
  
  -- TODO: podgląd po samym cond, bez stms
  --return afterCondTranss
  
  return afterBlockTranss

  -- TODO: map makeAlive resultUpdates

verDFSIfElse :: ModifyModuleType -> Exp -> Stm -> Stm -> Trans -> VerRes [Trans]
verDFSIfElse modifyModule cond ifBlock elseBlock tr = do
  -- TODO: determineExp?
  --let determinedCond = determineExp cond tr

  posCondTranss <- applyCond cond tr
  posTranss <- verDFSStm modifyModule ifBlock posCondTranss

  negCondTranss <- applyCond (negateExp cond) tr
  negTranss <- verDFSStm modifyModule elseBlock negCondTranss

  return $ posTranss ++ negTranss

