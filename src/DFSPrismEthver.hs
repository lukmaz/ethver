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
  newTrs <- applyToTrList modifyModule (evaluateExp modifyModule value) oldTrs
  applyToTrList modifyModule (addAssToTr modifyModule varIdent value) newTrs

verDFSStm modifyModule (SArrAss arrIdent index value) oldTrs = do
  newTrs <- applyToTrList modifyModule (evaluateExp modifyModule index) oldTrs >>= 
    applyToTrList modifyModule (evaluateExp modifyModule value)
  applyToTrList modifyModule (addArrAssToTr modifyModule arrIdent index value) newTrs

verDFSStm modifyModule (SIf cond ifBlock) trs = do
  condTranss <- applyToTrList modifyModule (evaluateExp modifyModule cond) trs
  applyToTrList modifyModule (updateIf modifyModule cond ifBlock) condTranss

verDFSStm modifyModule (SIfElse cond ifBlock elseBlock) trs = do
  condTranss <- applyToTrList modifyModule (evaluateExp modifyModule cond) trs
  applyToTrList modifyModule (updateIfElse modifyModule cond ifBlock elseBlock) condTranss

verDFSStm modifyModule (SWhile _ _) _ = do
  error $ "while loop not supported in verDFS"

  
---------
-- Ass --
---------

-- adds an assignment to a single transition
-- assumes value is evaluated
addAssToTr :: ModifyModuleType -> Ident -> Exp -> Trans -> VerRes [Trans]

addAssToTr modifyModule varIdent value oldTr = do
  newTr <- addAssToTrSingle varIdent value oldTr
  return [newTr]

-- simlarly, assumes index and value are evaluated
addArrAssToTr :: ModifyModuleType -> Ident -> Exp -> Exp -> Trans -> VerRes [Trans]

addArrAssToTr modifyModule arrIdent index value oldTr = do
  newTr <- addArrAssToTrSingle arrIdent index value oldTr
  return [newTr]

-- assumes value is evaluated
-- returns a SINGLE Trans
addAssToTrSingle :: Ident -> Exp -> Trans -> VerRes Trans

addAssToTrSingle varIdent value (trName, guards, updates) = do
  let determinedValue = determineExp value (trName, guards, updates)
  
  newUpdates <- foldM
    (\acc branch -> do
      partialUpdates <- addAssToUpdatesBranch varIdent determinedValue guards branch
      return $ partialUpdates ++ acc
    )
    []
    updates
  return (trName, guards, newUpdates)

-- assumes index and value are evaluated
-- returns a SINGLE Trans
addArrAssToTrSingle :: Ident -> Exp -> Exp -> Trans -> VerRes Trans

addArrAssToTrSingle arrIdent index value tr = do
  case determineExp (EArray arrIdent index) tr of
    EVar varIdent ->
      addAssToTrSingle varIdent value tr
    _ ->
      error $ "Cannot determine var name from array name after evaluation: " ++ (show $ EArray arrIdent index)

-- TODO random (może przepisać case exp z updatesFromAss z SmartFunPrismEthver.hs?
-- Aux: adds an assignment to an updates branch
addAssToUpdatesBranch :: Ident -> Exp -> [Exp] -> [(Ident, Exp)] -> VerRes [[(Ident, Exp)]]

addAssToUpdatesBranch varIdent value guards updatesBranch = do
  let 
    deleteOld :: [(Ident, Exp)] -> [(Ident, Exp)]
    deleteOld list = filter
      (\(i, _) -> i /= varIdent)
      list
    newUpdates =  
      (((varIdent, value):) . deleteOld)
      updatesBranch
  return [newUpdates]

--------
-- If --
--------

-- updateIf
updateIf :: ModifyModuleType -> Exp -> Stm -> Trans -> VerRes [Trans]
updateIf modifyModule cond ifBlock (trName, guards, updates) = do
  posTranss <- verDFSStm modifyModule ifBlock [(trName, cond:guards, updates)]
  let negTranss = [(trName, (negateExp cond):guards, updates)]

  return $ posTranss ++ negTranss

updateIfElse :: ModifyModuleType -> Exp -> Stm -> Stm -> Trans -> VerRes [Trans]
updateIfElse modifyModule cond ifBlock elseBlock (trName, guards, updates) = do
  posTranss <- verDFSStm modifyModule ifBlock [(trName, cond:guards, updates)]
  negTranss <- verDFSStm modifyModule elseBlock [(trName, (negateExp cond):guards, updates)]

  return $ posTranss ++ negTranss

