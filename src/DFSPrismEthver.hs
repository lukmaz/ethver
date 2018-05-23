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


-- Tu VerRes musi zostać, zeby dedukować typ zmiennej
verDFSStm :: ModifyModuleType -> Stm -> [Trans] -> VerRes [Trans]

verDFSStm modifyModule (SBlock []) trs = do
  return trs

verDFSStm modifyModule (SBlock (stmH:stmT)) trs = do
  verDFSStm modifyModule stmH trs >>= 
    verDFSStm modifyModule (SBlock stmT)

-- For a moment it returns only single Trans (and works for only simple ass)
-- nowe TODO: prawdopodobnie nie obsługuje bardziej skomplikowanych assow
verDFSStm modifyModule (SAss varIdent value) oldTrs = do
  --TODO: tak powinno być, ale nie działa z randomami
  {-applyToList 
    (\tr -> return [addSimpleAssesToTr [(varIdent, value)] tr]) 
    oldTrs
  -}
  -- TODO: tak działa z randomami
  applyToList (addAssToTr varIdent value) oldTrs

verDFSStm modifyModule (SIf cond ifBlock) trs = do
  applyToList (verDFSIf modifyModule cond ifBlock) trs

verDFSStm modifyModule (SIfElse cond ifBlock elseBlock) trs = do
  applyToList (verDFSIfElse modifyModule cond ifBlock elseBlock) trs

verDFSStm modifyModule (SWhile _ _) _ = do
  error $ "while loop not supported in verDFS"

verDFSStm modifyModule (SSend receiver amount) trs = do
  case receiver of
    EStr str -> do
      if (str == sNull)
        then applyToList (dfsBurnMoney amount) trs
        else error ".send can be applied only to 'null' or to an int"
    EInt receiverNumber -> do
      let receiverBalance = Ident $ sBalancePrefix ++ (show receiverNumber)
      applyToList (dfsTransferFromContract receiverBalance amount) trs
  

--------
-- If --
--------

-- verDFSIf
verDFSIfElse :: ModifyModuleType -> Exp -> Stm -> Stm -> Trans -> VerRes [Trans]
verDFSIfElse modifyModule cond ifBlock elseBlock tr@(trName, guards, updates) = do
  afterCondTranss <- applyCond (makeLeft cond) (trName, guards, updates)
  afterNegCondTranss <- applyCond (negateExp (makeLeft cond)) (trName, guards, updates)
  afterBlockTranss <- verDFSStm modifyModule ifBlock afterCondTranss
  afterNegBlockTranss <- verDFSStm modifyModule elseBlock afterNegCondTranss
  
  return $ map
    (\(trName, guards, updates) -> (trName, guards, map removeHeadLiv updates))
    (afterBlockTranss ++ afterNegBlockTranss)
      where
        removeHeadLiv :: Branch -> Branch
        removeHeadLiv (br, liv) = (br, tail liv)

verDFSIf :: ModifyModuleType -> Exp -> Stm -> Trans -> VerRes [Trans]
verDFSIf modifyModule cond ifBlock tr = 
  verDFSIfElse modifyModule cond ifBlock (SBlock []) tr

