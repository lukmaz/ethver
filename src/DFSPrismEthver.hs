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
    initUpdates = [[(stVar, EInt 1)]]
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
  newTrs <- applyToTrList (evaluateExp modifyModule value) oldTrs
  applyToTrList (addAssToTr varIdent value) newTrs

verDFSStm modifyModule (SArrAss arrIdent index value) oldTrs = do
  newTrs <- applyToTrList (evaluateExp modifyModule index) oldTrs >>= 
    applyToTrList (evaluateExp modifyModule value)
  applyToTrList (addArrAssToTr arrIdent index value) newTrs

verDFSStm modifyModule (SIf cond ifBlock) trs = do
  condTranss <- applyToTrList (evaluateExp modifyModule cond) trs
  applyToTrList (verDFSIf modifyModule cond ifBlock) condTranss

verDFSStm modifyModule (SIfElse cond ifBlock elseBlock) trs = do
  condTranss <- applyToTrList (evaluateExp modifyModule cond) trs
  applyToTrList (updateIfElse modifyModule cond ifBlock elseBlock) condTranss

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
  let determinedValue = determineExp value (trName, guards, updates)
  case determinedValue of
    ERand (EInt range) -> do
      newUpdates <- addRandomAssToUpdates varIdent range updates
      return [(trName, guards, newUpdates)]
    _ -> do
      newUpdates <- addAssToUpdates varIdent determinedValue updates
      return [(trName, guards, newUpdates)]

-- simlarly, assumes index and value are evaluated
addArrAssToTr :: Ident -> Exp -> Exp -> Trans -> VerRes [Trans]
addArrAssToTr arrIdent index value tr = do
  case determineExp (EArray arrIdent index) tr of
    EVar varIdent ->
      addAssToTr varIdent value tr
    _ ->
      error $ "Cannot determine var name from array name after evaluation: " ++ (show $ EArray arrIdent index)

-- adds a non-random assignment to updates
addAssToUpdates :: Ident -> Exp -> [[(Ident, Exp)]] -> VerRes [[(Ident, Exp)]]
addAssToUpdates varIdent value updates = do
  foldM
    (\acc branch -> do
      partialBranch <- addAssToUpdatesBranch varIdent value branch
      return $ partialBranch:acc
    )
    []
    updates

-- adds a random assignment to updates
addRandomAssToUpdates :: Ident -> Integer -> [[(Ident, Exp)]] -> VerRes [[(Ident, Exp)]]
addRandomAssToUpdates varIdent range updates = do
  foldM
    (\acc val -> do
      partialBranches <- addAssToUpdates varIdent (EInt val) updates
      return $ partialBranches ++ acc
    )
    []
    [0..(range - 1)]

-- adds a particular assignment to an updates branch
addAssToUpdatesBranch :: Ident -> Exp -> [(Ident, Exp)] -> VerRes [(Ident, Exp)]
addAssToUpdatesBranch varIdent value updatesBranch = do
  let 
    deleteOld :: [(Ident, Exp)] -> [(Ident, Exp)]
    deleteOld list = filter
      (\(i, _) -> i /= varIdent)
      list
    newBranch = (varIdent, value):(deleteOld updatesBranch)
  return newBranch

--------
-- If --
--------

-- updateIf
updateIf :: ModifyModuleType -> Exp -> Stm -> Trans -> VerRes [Trans]
updateIf modifyModule cond ifBlock tr = do
  let determinedCond = determineExp cond tr

  posCondTranss <- applyCond determinedCond tr
  posTranss <- verDFSStm modifyModule ifBlock posCondTranss

  negCondTranss <- applyCond (negateExp determinedCond) tr

  return $ posTranss ++ negCondTranss


-- TODO: zrobić jak updateIf
updateIfElse :: ModifyModuleType -> Exp -> Stm -> Stm -> Trans -> VerRes [Trans]
updateIfElse modifyModule cond ifBlock elseBlock tr = do
  let determinedCond = determineExp cond tr

  posCondTranss <- applyCond determinedCond tr
  posTranss <- verDFSStm modifyModule ifBlock posCondTranss

  negCondTranss <- applyCond (negateExp determinedCond) tr
  negTranss <- verDFSStm modifyModule elseBlock negCondTranss

  return $ posTranss ++ negTranss

