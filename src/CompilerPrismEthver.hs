module CompilerPrismEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import AbsEthver
import AuxPrismEthver
import AuxWorldPrismEthver
import CodePrismEthver
import ConstantsEthver
import DFSPrismEthver
import ExpPrismEthver
--import SmartFunPrismEthver
import WorldPrismEthver


-- generates (prism model code, prism properties)
verTree :: Program -> (String, String)
verTree prog =
  let (a, world) = (runState (verProgram prog)) emptyVerWorld
  in (generatePrism world, props world)

verProgram :: Program -> VerRes ()
verProgram (Prog users constants contract communication scenarios) = do
  mapM_ addUser users
  mapM_ addConstant constants

  addAutoVars

  verContractDecl contract
  verCommunicationDecl communication

  verContract contract
  verCommunication communication

  verScenarios scenarios
  addAdversarialContrTranss contract
  addAdversarialCommTranss communication
  addAdversarialBlockchainTranss

verContractDecl :: Contract -> VerRes ()
verContractDecl (Contr _ decls _) = do
  mapM_ (verDecl modifyContract) decls

verCommunicationDecl :: Communication -> VerRes ()
verCommunicationDecl (Comm decls _) = do
  mapM_ (verDecl modifyCommunication) decls

--------------
-- CONTRACT --
--------------

-- declarations already done before with verContractDecl
verContract :: Contract -> VerRes ()
verContract (Contr name _ funs) = do
  -- adds a command to blockchain module, that a function has just been broadcast by a particular player
  mapM_ (verFunBroadcast modifyPlayer0) funs
  -- adds two commands to blockchain module, that a transaction has been executed or not by a particular player
  -- depending if he holds enough money or not
  mapM_ (verFunExecute modifyPlayer0) funs

  -- analogous for second player
  mapM_ (verFunBroadcast modifyPlayer1) funs
  -- analogous for second player
  mapM_ (verFunExecute modifyPlayer1) funs

  -- adds to contract module a transaction that a particular player is executing the function
  verExecTransaction modifyPlayer0
  verExecTransaction modifyPlayer1

  -- adds to contract module  all commands generated from a particular function definition
  
  mapM_ verDFSFunContract funs
-------------------
-- COMMUNICATION --
-------------------

-- declarations already done before with verCommunicationDecl
verCommunication :: Communication -> VerRes ()
verCommunication (Comm _ funs) = do
  -- adds to communication module all commands generated from a particular function definition
  
  mapM_ verDFSFunCommunication funs

----------
-- Decl --
----------

verDecl :: ModifyModuleType -> Decl -> VerRes ()

verDecl modifyModule (Dec typ ident) = do
  addVar modifyModule typ ident
  --assignVarValue ident $ defaultValueOfType typ

verDecl modifyModule (DecInit typ ident value) = do
  addVar modifyModule typ ident
  addInitialValue modifyModule ident value

-- TODO: size inne niż 2
verDecl modifyModule (ArrDec typ (Ident ident) size) = do
  addVar modifyModule typ $ Ident $ ident ++ "_0"
  assignVarValue (Ident (ident ++ "_0")) $ defaultValueOfType typ
  addVar modifyModule typ $ Ident $ ident ++ "_1"
  assignVarValue (Ident (ident ++ "_1")) $ defaultValueOfType typ

------------------
-- verFunBroadcast
------------------
-- adds a command to blockchain module, that a function has just been broadcast by a particular player
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
      ENe (EVar $ Ident $ unident name ++ sStatusSuffix ++ (show $ number mod)) (EVar $ Ident sTBroadcast)
    ]
    -- TODO: ALive?
    [([(Ident $ unident name ++ sStatusSuffix ++ (show $ number mod), EVar (Ident sTBroadcast))], [Alive])]

----------------
-- verFunExecute
----------------
-- adds two commands to blockchain module, that a transaction has been executed or not by a particular player
-- depending if he holds enough money or not
verFunExecute :: ModifyModuleType -> Function -> VerRes ()

verFunExecute modifyModule (FunV name args stms) =
  verFunExecute modifyModule (Fun name args stms)

verFunExecute modifyModule (Fun name args stms) = do
  --TODO: argumenty
  mod <- modifyModule id

  let updates0 = [[
        (iContrSender, EInt $ number mod), 
        (iValue, EVar $ Ident $ unident name ++ sValueSuffix 
          ++ (show $ number mod)), (Ident $ unident name ++ sStatusSuffix 
          ++ (show $ number mod), EVar (Ident sTExecuted))]]
  let addAssignment acc (Ar _ varName) = acc ++ 
        [(createCoArgumentName name varName, EVar $ createScenarioArgumentName name varName $ number mod)]
  -- TODO: Alive?
  let updates = [(foldl addAssignment (head updates0) args, [Alive])]

  addTransNoState
    modifyBlockchain 
    (sBroadcastPrefix ++ (unident name))
    [
      EEq (EVar iContrState) (EInt nInitContrState),
      EEq 
        (EVar $ Ident $ unident name ++ sStatusSuffix ++ (show $ number mod)) 
        (EVar $ iTBroadcast),
      ELe 
        (EVar $ Ident $ unident name ++ sValueSuffix ++ (show $ number mod)) 
        (EVar $ Ident $ sBalancePrefix ++ (show $ number mod))
    ]
    updates

  addTransNoState
    modifyBlockchain 
    ""
    [
      EEq (EVar iContrState) (EInt nInitContrState),
      EEq 
        (EVar $ Ident $ unident name ++ sStatusSuffix ++ (show $ number mod)) 
        (EVar $ iTBroadcast),
      EGt 
        (EVar $ Ident $ unident name ++ sValueSuffix ++ (show $ number mod)) 
        (EVar $ Ident $ sBalancePrefix ++ (show $ number mod))
    ]
    -- TODO: Alive?
    [
      ([(Ident $ unident name ++ sStatusSuffix ++ (show $ number mod), EVar iTInvalidated)], [Alive])
    ]

------------------------
-- verExecTransaction --
------------------------

-- adds to contract module a transaction that a particular player is executing the function
verExecTransaction :: ModifyModuleType -> VerRes ()
verExecTransaction modifyModule = do
  mod <- modifyModule id
  addTransNoState
    modifyContract
    ""
    [
      EEq (EVar iContrState) (EInt 0),
      EEq (EVar iContrSender) (EInt $ number mod),
      EGe (EVar $ Ident $ sBalancePrefix ++ (show $ number mod)) (EVar iValue),
      ELe (EAdd (EVar iContractBalance) (EVar iValue)) (EVar iMaxContractBalance)
    ]
    -- TODO: Alive?
    [
      ([
        (iContrState, EVar $ iNextState),
        (Ident $ sBalancePrefix ++ (show $ number mod), 
          ESub (EVar $ Ident $ sBalancePrefix ++ (show $ number mod)) (EVar iValue)),
        (iContractBalance,
          EAdd (EVar iContractBalance) (EVar iValue))
      ], [Alive])
    ]

-------------------------------------
-- verDFSContract/Communication --
-------------------------------------

verDFSFunContractOrCommunication :: ModifyModuleType -> (Function -> VerRes ()) -> Function -> VerRes ()
verDFSFunContractOrCommunication modifyModule commonFun fun = do
  commonFun fun
  verDFSFun modifyModule fun

-----------------
-- verFunContract
-----------------

-- common for OLD, SMART and DFS
commonVerFunContract :: Function -> VerRes ()
commonVerFunContract (Fun name args stms) = do
  addFun (Fun name args stms)
  addContractFun (Fun name args stms)
  addVar modifyBlockchain (TUInt nTStates) $ Ident $ unident name ++ sStatusSuffix ++ "0" 
  addVar modifyBlockchain (TUInt nTStates) $ Ident $ unident name ++ sStatusSuffix ++ "1"

  mapM_ (addContrArgument name) args

  -- TODO: skąd wziąć zakres val - rozwiązane na razie jednym MAX_VALUE
  world <- get
  let maxValue = case Map.lookup (Ident sMaxValue) $ constants world of
        Just value -> value

  addVar modifyPlayer0 (TUInt (maxValue + 1)) $ Ident $ unident name ++ sValueSuffix ++ "0"
  addVar modifyPlayer1 (TUInt (maxValue + 1)) $ Ident $ unident name ++ sValueSuffix ++ "1"

  mod <- modifyContract id
  -- adds a command that the transaction is being broadcast
  addCustomTrans
    modifyContract
    (sBroadcastPrefix ++ (unident name))
    1
    0
    []
    -- TODO: Alive?
    [([(iNextState, EInt $ numStates mod + 1)], [Alive])]
  
  modifyContract (\mod -> mod {currState = numStates mod + 1, numStates = numStates mod + 1})

  return ()

-- DFS
verDFSFunContract :: Function -> VerRes ()
verDFSFunContract fun = verDFSFunContractOrCommunication modifyContract commonVerFunContract fun

-------------------------
-- verFunCommunication --
-------------------------

-- common for OLD, SMART and DFS
commonVerFunCommunication :: Function -> VerRes ()
commonVerFunCommunication (Fun funName args stms) = do
  addFun (Fun funName args stms)

  mapM_ (addCommArgument funName) args

  -- adds to Communication module  a command that the transaction is being communicated by a particular player
  addCommunicateOnePlayer funName args 0
  addCommunicateOnePlayer funName args 1
  
  mod <- modifyCommunication id
  let newState = numStates mod + 1
  _ <- modifyCommunication (setCurrState newState)
  _ <- modifyCommunication (setNumStates newState)

  return ()

-- DFS
verDFSFunCommunication :: Function -> VerRes ()
verDFSFunCommunication fun = verDFSFunContractOrCommunication modifyCommunication commonVerFunCommunication fun

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

  -- allow time elapse after scenario finish
  mod <- modifyModule id

  addCustomTrans
    modifyModule
    sTimelockStep
    (currState mod)
    (currState mod)
    []
    [([], [Alive])]

  --------------------------------------------------
  -- TUTAJ ZAKOMENTOWAĆ, ŻEBY NIE BYŁO CRIT. SEC. --
  --------------------------------------------------

  -- add critical sections stuff 
  _ <- modifyModule addCS2
  
  -- TODO: zmienić 0 i 1 na stałe
  addFirstCustomTrans
    modifyModule
    ""
    0
    1
    [ENe (EVar iAdversaryFlag) (EInt $ number mod)]
    -- TODO: Alive?
    [([], [Alive])]

  addCustomTrans
    modifyModule
    ""
    0
    (-1)
    [EEq (EVar iAdversaryFlag) (EInt $ number mod)]
    -- TODO: Alive?
    [([], [Alive])]

  -- allow ADV to push the timelock at any time
  addCustomTrans
    modifyModule
    (sTimelockStep)
    (-1)
    (-1)
    []
    [([], [Alive])]

  -- two transitions for ability for adversary to interrupt the protocol
  -- this one not needed anymore, since the timeStep is called in blockchain module
  {- addCustomTrans
    modifyModule
    (sTimelockStep ++ (show $ number mod))
    (-1)
    (-1)
    [EEq (EVar iContrState) (EInt 1),
      EEq (EVar iCommState) (EInt 1)]
    -- TODO: Alive?
    [([], [Alive])]
  -}

  -- moved to addAdversarialBlockchainTranss in AuxWorldPrismEthver.hs
  -- world <- get
  {-addTransNoState
    modifyBlockchain
    (sTimelockStep ++ (show $ number mod))
    (
      (ELt (EVar $ Ident $ sTimeElapsed) (EVar $ Ident $ sMaxTime))
        : (Map.elems $ Map.map
            (\fun -> ENe
              (EVar $ Ident $ (nameOfFunction fun) ++ sStatusSuffix ++ "0")
              (EVar iTBroadcast)
            )
            (contractFuns world)
          )
        ++ (Map.elems $ Map.map
            (\fun -> ENe
              (EVar $ Ident $ (nameOfFunction fun) ++ sStatusSuffix ++ "1")
              (EVar iTBroadcast)
            )
            (contractFuns world)
          )
    )
    -- TODO: Alive?
    [([(Ident sTimeElapsed, EAdd (EVar $ Ident sTimeElapsed) (EInt 1))], [Alive])]
    -}
