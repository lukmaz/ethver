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

verDFSStm :: ModifyModuleType -> Stm -> [Trans] -> VerRes [Trans]

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

-- OLD: wersja z evaluateArray:
{-verDFSStm modifyModule (SAss varIdent value) oldTrs = do
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
-}

-- nowe TODO: prawdopodobnie nie obsługuje bardziej skomplikowanych assow
verDFSStm modifyModule (SAss varIdent value) oldTrs = do
  --TODO: tak powinno być, ale nie działa z randomami
  {-applyToList 
    (\tr -> return [addSimpleAssesToTr [(varIdent, value)] tr]) 
    oldTrs
  -}
  -- TODO: tak działa z randomami
  applyToList (addAssToTr varIdent value) oldTrs

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

verDFSStm modifyModule (SSend receiver amount) trs = do
  case receiver of
    EInt receiverNumber -> do
      let receiverBalance = Ident $ sBalancePrefix ++ (show receiverNumber)
      applyToList (dfsTransferFromContract receiverBalance amount) trs
  

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

