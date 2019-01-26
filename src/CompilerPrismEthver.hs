module CompilerPrismEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import AbsEthver
import AuxEthver
import AuxPrismEthver
import AuxWorldPrismEthver
import CodePrismEthver
import ConstantsEthver
import DFSPrismEthver
import ExpPrismEthver
--import SmartFunPrismEthver
import WorldPrismEthver


-- generates (prism model code, prism properties)
verTree :: Program -> String
verTree prog =
  let (a, world) = (runState (verProgram prog)) emptyVerWorld
  in generatePrism world

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
  
  --Should be fused into open.sendTransaction() etc.
  --addAdversarialRCmt
  --addAdversarialOCmt - already fused

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
  
  --mapM_ verDFSFunContract funs
  mapM_ verOldFunContract funs

-------------------
-- COMMUNICATION --
-------------------

-- declarations already done before with verCommunicationDecl
verCommunication :: Communication -> VerRes ()
verCommunication (Comm _ funs) = do
  -- adds to communication module all commands generated from a particular function definition
  
  --mapM_ verDFSFunCommunication funs
  mapM_ verOldFunCommunication funs

----------
-- Decl --
----------

verDecl :: ModifyModuleType -> Decl -> VerRes ()

verDecl modifyModule (Dec (TCUInt range) varIdent) = do
  world <- get
  let 
    --nr = fromIntegral $ Map.size $ commitmentsIds world
    idIdent = Ident $ unident varIdent ++ sIdSuffix
    --globalIdent = Ident $ sGlobalCommitments ++ "_" ++ show nr
  --put (world {commitmentsIds = Map.insert varIdent nr $ commitmentsIds world})
  
  -- add TCUInt variable with the exact given name
  
  --
  -- TODO: is it needed? since the value is already stored in global commitment? Temporarily removed
  -- _ <- modifyModule (addVarToModule (TCUInt range) varIdent)
  --

  -- addInitialValue modifyModule globalIdent (EInt $ range + 1)

  -- add gloabl_commitment variable
  -- (OLD)
  -- _ <- modifyModule (addGlobalCommitment (TCUInt range) globalIdent)
  -- addInitialValue modifyModule globalIdent (EInt $ range + 1)
  -- (NEW)
  addGlobalCommitments range

  -- auxiliary variable for id with the given name
  addCmtIdVar modifyModule idIdent

  mod <- modifyModule id 
  addInitialValue modifyModule idIdent (EInt $ number mod)


verDecl modifyModule (Dec typ ident) = do
  addVar modifyModule typ ident
  --assignVarValue ident $ defaultValueOfType typ

verDecl modifyModule (DecInit typ ident value) = do
  addVar modifyModule typ ident
  addInitialValue modifyModule ident value

-- TODO: size inne niż 2
verDecl modifyModule (ArrDec typ (Ident ident) size) = do
  verDecl modifyModule (Dec typ $ Ident $ ident ++ "_0")
  verDecl modifyModule (Dec typ $ Ident $ ident ++ "_1")

-- OLD:
{-verDecl modifyModule (ArrDec typ (Ident ident) size) = do
  addVar modifyModule typ $ Ident $ ident ++ "_0"
  assignVarValue (Ident (ident ++ "_0")) $ defaultValueOfType typ
  addVar modifyModule typ $ Ident $ ident ++ "_1"
  assignVarValue (Ident (ident ++ "_1")) $ defaultValueOfType typ
-}
------------------
-- verFunBroadcast
------------------
-- adds a command to blockchain module, that a function has just been broadcast by a particular player
verFunBroadcast :: ModifyModuleType -> Function -> VerRes ()

verFunBroadcast modifyModule (FunV name args stms) = 
  verFunBroadcast modifyModule (Fun name args stms)

verFunBroadcast modifyModule (FunL _ name args stms) =
  verFunBroadcast modifyModule (Fun name args stms)

verFunBroadcast modifyModule (FunVL _ name args stms) =
  verFunBroadcast modifyModule (Fun name args stms)

verFunBroadcast modifyModule (Fun name args stms) = do
  --TODO: argumenty
  mod <- modifyModule id
  addTransNoState
    modifyBlockchain 
    (sBroadcastPrefix ++ (unident name) ++ (show $ number mod))
    [
      EEq (EVar iContrState) (EInt nInitContractState), 
      EEq (EVar iCommState) (EInt nInitCommState), 
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

verFunExecute modifyModule (FunL _ name args stms) =
  verFunExecute modifyModule (Fun name args stms)

verFunExecute modifyModule (FunVL _ name args stms) =
  verFunExecute modifyModule (Fun name args stms)

verFunExecute modifyModule (Fun name args stms) = do
  --TODO: argumenty
  mod <- modifyModule id

  let 
    updates0 = [[
        (iContrSender, EInt $ number mod), 
        (iValue, EVar $ Ident $ unident name ++ sValueSuffix 
          ++ (show $ number mod)), (Ident $ unident name ++ sStatusSuffix 
          ++ (show $ number mod), EVar (Ident sTExecuted))]]
    addAssignment acc (Ar (TCUInt _) varName) = acc 
        ++ [(createCoArgumentName sIdSuffix name varName, 
          EVar $ createScenarioArgumentName sIdSuffix name varName $ number mod)] 
        -- ++ [(createCoArgumentName "" name varName, EVar $ createScenarioArgumentName "" name varName $ number mod)]
    addAssignment acc (Ar _ varName) = acc ++ 
        [(createCoArgumentName "" name varName, EVar $ createScenarioArgumentName "" name varName $ number mod)]
  -- TODO: Alive?
    updates = [(foldl addAssignment (head updates0) args, [Alive])]

  addTransNoState
    modifyBlockchain 
    (sBroadcastPrefix ++ (unident name))
    [
      EEq (EVar iContrState) (EInt nInitContractState),
      EEq (EVar iCommState) (EInt nInitCommState),
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
      EEq (EVar iContrState) (EInt nInitContractState),
      EEq (EVar iCommState) (EInt nInitCommState),
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
{-
verDFSFunContractOrCommunication :: ModifyModuleType -> (Function -> VerRes ()) -> Function -> VerRes ()
verDFSFunContractOrCommunication modifyModule commonFun fun = do
  commonFun fun
  verDFSFun modifyModule fun
-}

----------------------------------
-- verOldContract/Communication --
-- limit, big if for sender,    --
-- all statements               --
----------------------------------

verOldFunContractOrCommunication :: ModifyModuleType -> (Function -> VerRes ()) -> Function -> VerRes ()

verOldFunContractOrCommunication modifyModule commonfun (FunV name args stm) =
  verOldFunContractOrCommunication modifyModule commonfun (FunL (-1)  name args stm)

verOldFunContractOrCommunication modifyModule commonfun (Fun name args stm) =
  verOldFunContractOrCommunication modifyModule commonfun (FunL (-1)  name args stm)

verOldFunContractOrCommunication modifyModule commonfun (FunVL limit name args stm) =
  verOldFunContractOrCommunication modifyModule commonfun (FunL limit  name args stm)

verOldFunContractOrCommunication modifyModule commonFun fun@(FunL limit name args stms) = do
  commonFun fun

  -- limit number of runs of each function
  if limit > 0 then do
    addVar modifyPlayer0 (TUInt (limit + 1)) (Ident $ unident name ++ sRunsSuffix ++ "0") 
    addVar modifyPlayer1 (TUInt (limit + 1)) (Ident $ unident name ++ sRunsSuffix ++ "1") 
  else
    return ()


  -- one if for msg.sender
  mod <- modifyModule id
  let actualSender = whichSender mod

  world <- get
  put (world {senderNumber = Just 0})

  verStm modifyModule $
    SIf (EEq (EVar actualSender) (EInt 0)) (SBlock stms)

  world <- get
  put (world {senderNumber = Just 1})

  verStm modifyModule $
    SIf (EEq (EVar actualSender) (EInt 1)) (SBlock stms)

  world <- get
  put (world {senderNumber = Nothing})
  
  -- final command
  mod <- modifyModule id
  addCustomTrans
    modifyModule
    ""
    (currState mod)
    1
    []
    [([], [Alive])]

-----------------
-- verFunContract
-----------------

-- common for OLD, SMART and DFS
-- arguments are handled here
commonVerFunContract :: Function -> VerRes ()
commonVerFunContract (FunL _ name args stms) =
  commonVerFunContract (Fun name args stms)

commonVerFunContract (Fun name args stms) = do
  -- adds fun ident to two maps in World
  addFun (Fun name args stms)
  addContractFun (Fun name args stms)
  -- variables for status of the transaction
  addVar modifyBlockchain (TUInt nTStates) $ Ident $ unident name ++ sStatusSuffix ++ "0" 
  addVar modifyBlockchain (TUInt nTStates) $ Ident $ unident name ++ sStatusSuffix ++ "1"

  -- add arguments variables to World
  mapM_ (addContrArgument name) args

  -- TODO: skąd wziąć zakres val - rozwiązane na razie jednym MAX_VALUE
  world <- get
  let maxValue = case Map.lookup (Ident sMaxValue) $ constants world of
        Just value -> value

  -- add arguments for value to players modules
  addVar modifyPlayer0 (TUInt (maxValue + 1)) $ Ident $ unident name ++ sValueSuffix ++ "0"
  addVar modifyPlayer1 (TUInt (maxValue + 1)) $ Ident $ unident name ++ sValueSuffix ++ "1"
  
  mod <- modifyContract id
  -- adds a command to Contract module that the transaction is being broadcast
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
--verDFSFunContract :: Function -> VerRes ()
--verDFSFunContract fun = verDFSFunContractOrCommunication modifyContract commonVerFunContract fun

verOldFunContract :: Function -> VerRes ()
verOldFunContract fun = verOldFunContractOrCommunication modifyContract commonVerFunContract fun

-------------------------
-- verFunCommunication --
-------------------------

-- common for OLD, SMART and DFS
commonVerFunCommunication :: Function -> VerRes ()

commonVerFunCommunication (FunL _ funName args stms) =
  commonVerFunCommunication (Fun funName args stms)

commonVerFunCommunication (Fun funName args stms) = do
  addFun (Fun funName args stms)

  mapM_ (addCommArgument funName) args

  -- adds to Communication module  a command that the transaction is being communicated by a particular player
  addCommunicateOnePlayer funName args 0
  addCommunicateOnePlayer funName args 1
  
  mod <- modifyCommunication id
  let newState = numStates mod + 2
  _ <- modifyCommunication (setCurrState newState)
  _ <- modifyCommunication (setNumStates newState)

  return ()

-- DFS
-- verDFSFunCommunication :: Function -> VerRes ()
-- verDFSFunCommunication fun = verDFSFunContractOrCommunication modifyCommunication commonVerFunCommunication fun

-- OLD
verOldFunCommunication :: Function -> VerRes ()
verOldFunCommunication fun = verOldFunContractOrCommunication modifyCommunication commonVerFunCommunication fun

--------------
-- SCENARIO --
--------------

verScenarios :: [Scenario] -> VerRes ()
verScenarios [(Scen userName0 decls0 stms0), (Scen userName1 decls1 stms1)] = do
  --TODO: przepadają userName'y
  mapM_ (verDecl modifyPlayer0) decls0
  mapM_ (verDecl modifyPlayer1) decls1

  verScenario modifyPlayer0 decls0 stms0
  verScenario modifyPlayer1 decls1 stms1

verScenario :: ModifyModuleType -> [Decl] -> [Stm] -> VerRes ()
verScenario modifyModule decls stms = do
  mod <- modifyModule id

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

