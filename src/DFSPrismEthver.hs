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

-- TODO: zlikwidować jeden krok pośredni. Przekopoiować tu zawartość funkcji addAssToTr. A może nie? (Bo tr/trs)
verDFSStm modifyModule (SAss varIdent value) trs = do
  applyToTrList modifyModule (addAssToTr modifyModule (SAss varIdent value)) trs

verDFSStm modifyModule (SArrAss arrIdent index value) trs = do
  applyToTrList modifyModule (addAssToTr modifyModule (SArrAss arrIdent index value)) trs

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

-- assumes Stm is evaluated.
-- TODO: One function for all Stms?
-- Małe TODO: mógłby zwracać jedno Trans zamiast listy. Ale to chyba nie problem
addAssToTrSingle :: Stm -> Trans -> VerRes Trans

addAssToTrSingle (SAss varIdent value) (trName, guards, updates) = do
  let determinedValue = determineExp value (trName, guards, updates)
  
  newUpdates <- foldM
    (\acc branch -> do
      partialUpdates <- addAssToUpdatesBranch guards (SAss varIdent determinedValue) branch
      return $ partialUpdates ++ acc
    )
    []
    updates
  return (trName, guards, newUpdates)

addAssToTrSingle (SArrAss arrIdent index value) tr = do
  case determineExp (EArray arrIdent index) tr of
    EVar varIdent ->
      addAssToTrSingle (SAss varIdent value) tr
    _ ->
      error $ "Cannot determine var name from array name after evaluation: " ++ (show $ EArray arrIdent index)

-- adds an assignment to a single transition
-- can possibly create longer list of updates in case the array index is not known
addAssToTr :: ModifyModuleType -> Stm -> Trans -> VerRes [Trans]

-- TODO: zmienic nazewnictwo. Niech addDFSSTm robi evaluateExp i niech odpala addAssToTr(Single?)
addAssToTr modifyModule (SAss varIdent value) oldTr = do
  trs <- evaluateExp modifyModule value oldTr 
  applyToTrList 
    modifyModule 
    (\tr -> do
      newTr <- addAssToTrSingle (SAss varIdent value) tr
      return [newTr]
    )
    trs

addAssToTr modifyModule (SArrAss arrIdent index value) oldTr = do
  trs <- evaluateExp modifyModule index oldTr >>= applyToTrList modifyModule (evaluateExp modifyModule value)
  applyToTrList
    modifyModule
    (\tr -> do
      newTr <- addAssToTrSingle (SArrAss arrIdent index value) tr
      return [newTr]
    )
    trs


-- modifyModule niepotrzebne?
-- TODO: only simple assignments for a moment
-- TODO: random
-- Aux: adds an assignment to an updates branch
-- can possibly create longer list of updates for randomized assignment
addAssToUpdatesBranch :: [Exp] -> Stm -> [(Ident, Exp)] -> VerRes [[(Ident, Exp)]]

addAssToUpdatesBranch guards (SAss ident exp) updatesBranch = do
  -- TODO random (może przepisać case exp z updatesFromAss z SmartFunPrismEthver.hs?
  let 
    deleteOld :: [(Ident, Exp)] -> [(Ident, Exp)]
    deleteOld list = filter
      (\(i, _) -> i /= ident)
      list
    newUpdates =  
      (((ident, exp):) . deleteOld)
      updatesBranch
  return [newUpdates]

addAssToUpdatesBranch _  (SArrAss arrName index exp) _ = do
  error $ "addAssToUpdateBranch should not be called with SArrAss (" ++ (show $ SArrAss arrName index exp)
  
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

