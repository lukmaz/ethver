module CompilerPrismEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map

import AbsEthver
import AuxPrismEthver
import AuxWorldPrismEthver
import CodePrismEthver
import ConstantsEthver
import ExpPrismEthver
import WorldPrismEthver


-- TODO: zliczanie stanów

-- generates (prism model code, prism properties)
verTree :: Program -> (String, String)
verTree prog =
  let (a, world) = (runState (verProgram prog)) emptyVerWorld
  in (generatePrism world, props world)

verProgram :: Program -> VerRes ()
verProgram (Prog users constants contract communication scenarios) = do
  mapM_ addUser users
  mapM_ addConstant constants

  verContract contract
  verCommunication communication
  verScenarios scenarios
  addAdversarialTranss contract

addAdversarialTranss :: Contract -> VerRes ()
addAdversarialTranss (Contr _ _ funs) = do
  mapM_ (addAdversarialTranssToPlayer modifyPlayer0) funs
  mapM_ (addAdversarialTranssToPlayer modifyPlayer1) funs

--------------
-- CONTRACT --
--------------

verContract :: Contract -> VerRes ()
verContract (Contr name decls funs) = do
  mapM_ verCoDecl decls
  
  mapM_ (verFunBroadcast modifyPlayer0) funs
  mapM_ (verFunExecute modifyPlayer0) funs
  mapM_ (verFunBroadcast modifyPlayer1) funs
  mapM_ (verFunExecute modifyPlayer1) funs

  verExecTransaction modifyPlayer0
  verExecTransaction modifyPlayer1

  mapM_ verFunContract funs

verCommunication :: Communication -> VerRes ()
verCommunication (Comm decls funs) = do
  mapM_ verCommDecl decls

  --TODO: verFunBroadcast? 
  --TODO: verFunExecute?
  --TODO: verExecTransaction?

  mapM_ verFunCommunication funs

-- TODO: globalne, nieglobalne
verCoDecl :: Decl -> VerRes ()
verCoDecl (Dec typ ident) = do
  addContrVar typ ident


-- TODO: size inne niż 2
verCoDecl (ArrDec typ (Ident ident) size) = do
  addContrVar typ $ Ident $ ident ++ "_0"
  addContrVar typ $ Ident $ ident ++ "_1"

verCommDecl :: Decl -> VerRes ()

verCommDecl (Dec typ ident) = do
  addCommVar typ ident

--TODO: size inne niż 2
verCommDecl (ArrDec typ (Ident ident) size) = do
  addCommVar typ $ Ident $ ident ++ "_0"
  addCommVar typ $ Ident $ ident ++ "_1"


verFunBroadcast :: ModifyModuleType -> Function -> VerRes ()

verFunBroadcast modifyModule (FunV name args stms) = 
  verFunBroadcast modifyModule (Fun name args stms)

verFunBroadcast modifyModule (Fun name args stms) = do
  --TODO: argumenty
  mod <- modifyModule id
  addTransNoState
    modifyBlockchain 
    (sBroadcastPrefix ++ (unident name) ++ (show $ number mod))
    [
      EEq (EVar iContrState) (EInt 1), 
      ENe (EVar $ Ident $ unident name ++ sStateSufix ++ (show $ number mod)) (EVar $ Ident sTBroadcast)
    ]
    [[(Ident $ unident name ++ sStateSufix ++ (show $ number mod), EVar (Ident sTBroadcast))]]

verFunExecute :: ModifyModuleType -> Function -> VerRes ()

verFunExecute modifyModule (FunV name args stms) =
  verFunExecute modifyModule (Fun name args stms)

verFunExecute modifyModule (Fun name args stms) = do
  --TODO: argumenty
  mod <- modifyModule id

  let updates0 = [[
        (iSender, EInt $ number mod), 
        (iValue, EVar $ Ident $ unident name ++ sValueSufix 
          ++ (show $ number mod)), (Ident $ unident name ++ sStateSufix 
          ++ (show $ number mod), EVar (Ident sTExecuted))]]
  let addAssignment acc (Ar _ (Ident varName)) = acc ++ 
        [(Ident $ unident name ++ "_" ++ varName, EVar $ Ident $ unident name ++ "_" 
          ++ varName ++ (show $ number mod))]
  let updates = [foldl addAssignment (head updates0) args]

  addTransNoState
    modifyBlockchain 
    (sBroadcastPrefix ++ (unident name))
    [
      EEq (EVar iContrState) (EInt nInitContrState),
      EEq 
        (EVar $ Ident $ unident name ++ sStateSufix ++ (show $ number mod)) 
        (EVar $ iTBroadcast),
      ELe 
        (EVar $ Ident $ unident name ++ sValueSufix ++ (show $ number mod)) 
        (EVar $ Ident $ sBalancePrefix ++ (show $ number mod))
    ]
    updates

  addTransNoState
    modifyBlockchain 
    ""
    [
      EEq (EVar iContrState) (EInt nInitContrState),
      EEq 
        (EVar $ Ident $ unident name ++ sStateSufix ++ (show $ number mod)) 
        (EVar $ iTBroadcast),
      EGt 
        (EVar $ Ident $ unident name ++ sValueSufix ++ (show $ number mod)) 
        (EVar $ Ident $ sBalancePrefix ++ (show $ number mod))
    ]
    [
      [(Ident $ unident name ++ sStateSufix ++ (show $ number mod), EVar iTInvalidated)]
    ]

verFunContract :: Function -> VerRes ()

verFunContract (FunV name args stms) = 
  verFunContract (Fun name args stms) 

verFunContract (Fun name args stms) = do
  addFun (Fun name args stms)
  addBcVar (TUInt nTStates) $ Ident $ unident name ++ sStateSufix ++ "0" 
  addBcVar (TUInt nTStates) $ Ident $ unident name ++ sStateSufix ++ "1"

  -- adds also to argMap
  mapM_ (addArgument name) args

  -- TODO: skąd wziąć zakres val?
  addP0Var (TUInt 3) $ Ident $ unident name ++ sValueSufix ++ "0"
  addP1Var (TUInt 3) $ Ident $ unident name ++ sValueSufix ++ "1"

  mod <- modifyContract id
  addCustomTrans
    modifyContract
    (sBroadcastPrefix ++ (unident name))
    1
    0
    []
    [[(iNextState, EInt $ numStates mod + 1)]]
  
  modifyContract (\mod -> mod {currState = numStates mod + 1, numStates = numStates mod + 1})
  
  mapM_ (verStm modifyContract) stms

  mod <- modifyContract id
  addCustomTrans
    modifyContract
    ""
    (numStates mod)
    1
    []
    [[]]
  
  clearArgMap



-- COMMUNICATION

verFunCommunication :: Function -> VerRes ()

-- TODO
verFunCommunication _ = return ()



verExecTransaction :: ModifyModuleType -> VerRes ()
verExecTransaction modifyModule = do
  mod <- modifyModule id
  addTransNoState
    modifyContract
    ""
    [
      EEq (EVar iContrState) (EInt 0),
      EEq (EVar iSender) (EInt $ number mod),
      EGe (EVar $ Ident $ sBalancePrefix ++ (show $ number mod)) (EVar iValue),
      ELe (EAdd (EVar iContractBalance) (EVar iValue)) (EVar iMaxContractBalance)
    ]
    [[
      (iContrState, EVar $ iNextState),
      (Ident $ sBalancePrefix ++ (show $ number mod), 
        ESub (EVar $ Ident $ sBalancePrefix ++ (show $ number mod)) (EVar iValue)),
      (iContractBalance,
        EAdd (EVar iContractBalance) (EVar iValue))
    ]]


--------------
-- SCENARIO --
--------------

verScenarios :: [Scenario] -> VerRes ()
verScenarios [(Scen userName0 decls0 stms0), (Scen userName1 decls1 stms1)] = do
  --TODO: przepadają userName'y
  verScenario modifyPlayer0 decls0 stms0
  verScenario modifyPlayer1 decls1 stms1

verScenario :: ModifyModuleType -> [Decl] -> [Stm] -> VerRes ()
verScenario modifyModule decls stms = do
  mod <- modifyModule id

  mapM_ (verDecl modifyModule) decls

  mapM_ (verStm modifyModule) stms


  --------------------------------------------------
  -- TUTAJ ZAKOMENTOWAĆ, ŻEBY NIE BYŁO CRIT. SEC. --
  --------------------------------------------------

  -- add critical sections stuff 
  _ <- modifyModule addCS
  
  -- TODO: zmienić 0 i 1 na stałe
  addFirstCustomTrans
    modifyModule
    ""
    0
    1
    [ENe (EVar iAdversaryFlag) (EInt $ number mod)]
    [[]]

  addCustomTrans
    modifyModule
    ""
    0
    (-1)
    [EEq (EVar iAdversaryFlag) (EInt $ number mod)]
    [[]]

----------
-- Decl --
----------

verDecl :: ModifyModuleType -> Decl -> VerRes ()
verDecl modifyModule (Dec typ ident) = do
  addVar modifyModule typ ident

