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
  
verContractDecl :: Contract -> VerRes ()
verContractDecl (Contr _ decls _ _) = do
  mapM_ (verDecl modifyContract) decls

verCommunicationDecl :: Communication -> VerRes ()
verCommunicationDecl (Comm decls _) = do
  mapM_ (verDecl modifyCommunication) decls

--------------
-- CONTRACT --
--------------

-- declarations already done before with verContractDecl
verContract :: Contract -> VerRes ()
verContract (Contr name _ _ funs) = do
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
  
  mapM_ verOldFunCommunication funs

----------
-- Decl --
----------

verDecl :: ModifyModuleType -> Decl -> VerRes ()

verDecl modifyModule (Dec (TCUInt range) varIdent) = do
  addGlobalCommitments range

  -- auxiliary variable for id with the given name
  mod <- modifyModule id 
  addCmtIdVar modifyModule varIdent
  addInitialValue modifyModule varIdent (EInt $ number mod)

verDecl modifyModule (Dec (TSig sigTypes) varIdent) = do
  addGlobalSignatures (TSig sigTypes)

  -- auxiliary variable for id with the given name
  mod <- modifyModule id
  addSigIdVar modifyModule (TSig sigTypes) varIdent

verDecl modifyModule (Dec typ ident) = do
  addVar modifyModule typ ident

verDecl modifyModule (DecInit typ ident EGetMy) = do
  mod <- modifyModule id
  addVar modifyModule typ ident
  addInitialValue modifyModule ident $ EInt $ number mod

verDecl modifyModule (DecInit typ ident value) = do
  addVar modifyModule typ ident
  addInitialValue modifyModule ident value

verDecl modifyModule (ArrDec typ (Ident ident) size) = do
  verDecl modifyModule (Dec typ $ Ident $ ident ++ "_0")
  verDecl modifyModule (Dec typ $ Ident $ ident ++ "_1")

verDecl modifyModule (MapDec typ ident) = do
  verDecl modifyModule (ArrDec typ ident 2)

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

generateCommonBroadcastGuards :: Ident -> Integer -> [Exp]
generateCommonBroadcastGuards funIdent nr = 
  [
    EEq (EVar iContrState) (EInt nInitContractState),
    EEq (EVar iCommState) (EInt nInitCommState),
    EEq
      (EVar $ Ident $ unident funIdent ++ sStatusSuffix ++ (show nr))
      (EVar $ iTBroadcast)
  ]

generateCommonBroadcastUpdates :: Ident -> Integer -> [(Ident, Exp)]
generateCommonBroadcastUpdates funIdent nr = 
  [
    (iContrSender, EInt nr), 
    (Ident $ unident funIdent ++ sStatusSuffix ++ (show nr), EVar (Ident sTExecuted))
  ]

addAssignmentToUpdates :: Ident -> Integer -> [(Ident, Exp)] -> Arg -> [(Ident, Exp)]
addAssignmentToUpdates funIdent nr acc (Ar _ varIdent) = acc ++ 
  [(createCoArgumentName "" funIdent varIdent, 
    EVar $ createScenarioArgumentName "" funIdent varIdent nr)]

verFunExecute :: ModifyModuleType -> Function -> VerRes ()

verFunExecute modifyModule (FunV name args stms) = do
  mod <- modifyModule id

  let
    guards0 = generateCommonBroadcastGuards name (number mod)
    updates0 = generateCommonBroadcastUpdates name (number mod)
    updates1 = 
      [
        updates0 ++
        [(iValue, EVar $ Ident $ unident name ++ sValueSuffix 
          ++ (show $ number mod))]
      ]
  -- TODO: Alive?
    updates = [(foldl (addAssignmentToUpdates name (number mod)) (head updates1) args, [Alive])]

  addTransNoState
    modifyBlockchain 
    (sBroadcastPrefix ++ (unident name))
    (guards0 ++
      [
        ELe 
          (EVar $ Ident $ unident name ++ sValueSuffix ++ (show $ number mod)) 
          (EVar $ Ident $ sBalancePrefix ++ (show $ number mod))
      ]
    )
    updates

  addTransNoState
    modifyBlockchain 
    ""
    (guards0 ++
      [
        EGt 
          (EVar $ Ident $ unident name ++ sValueSuffix ++ (show $ number mod)) 
          (EVar $ Ident $ sBalancePrefix ++ (show $ number mod))
      ]
    )
    -- TODO: Alive?
    [
      ([(Ident $ unident name ++ sStatusSuffix ++ (show $ number mod), EVar iTInvalidated)], [Alive])
    ]

verFunExecute modifyModule (Fun name args stms) = do
  mod <- modifyModule id

  let
    guards0 = generateCommonBroadcastGuards name (number mod)
    updates0 = generateCommonBroadcastUpdates name (number mod)
    updates1 = 
      [
        updates0 ++
        [(iValue, EInt 0)]
      ]
    -- TODO: Alive?
    updates = [(foldl (addAssignmentToUpdates name (number mod)) (head updates1) args, [Alive])]

  addTransNoState
    modifyBlockchain 
    (sBroadcastPrefix ++ (unident name))
    guards0
    updates

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

-- add function before hiding its real type
verFunAux :: ModifyModuleType -> (Function -> VerRes ()) -> Function -> VerRes ()
verFunAux modifyModule commonFun fun = do

  verOldFunContractOrCommunication modifyModule commonFun fun

----------------------------------
-- verOldContract/Communication --
-- big if for sender,    --
-- all statements               --
----------------------------------

verOldFunContractOrCommunication :: ModifyModuleType -> (Function -> VerRes ()) -> Function -> VerRes ()

verOldFunContractOrCommunication modifyModule commonfun (FunV name args stm) = do
  -- TODO: skąd wziąć zakres val - rozwiązane na razie jednym MAX_VALUE
  world <- get
  let maxValue = case Map.lookup (Ident sMaxValue) $ constants world of
        Just value -> value

  -- add arguments for value to players modules
  addVar modifyPlayer0 (TUInt (maxValue + 1)) $ Ident $ unident name ++ sValueSuffix ++ "0"
  addVar modifyPlayer1 (TUInt (maxValue + 1)) $ Ident $ unident name ++ sValueSuffix ++ "1"

  verOldFunContractOrCommunication modifyModule commonfun (Fun name args stm)

verOldFunContractOrCommunication modifyModule commonFun fun@(Fun name args stms) = do
  commonFun fun

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

commonVerFunContract (Fun name args stms) = do
  -- variables for status of the transaction
  addVar modifyBlockchain (TUInt nTStates) $ Ident $ unident name ++ sStatusSuffix ++ "0" 
  addVar modifyBlockchain (TUInt nTStates) $ Ident $ unident name ++ sStatusSuffix ++ "1"

  -- add arguments variables to World
  mapM_ (addContrArgument name) args

  
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

verOldFunContract :: Function -> VerRes ()
verOldFunContract fun = do
  -- adds fun ident to two maps in World
  addFun fun
  addContractFun fun

  verFunAux modifyContract commonVerFunContract fun

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
  let newState = numStates mod + 2
  _ <- modifyCommunication (setCurrState newState)
  _ <- modifyCommunication (setNumStates newState)

  return ()

-- OLD
verOldFunCommunication :: Function -> VerRes ()
verOldFunCommunication fun = do
  -- adds fun ident to two maps in World
  addFun fun

  verFunAux modifyCommunication commonVerFunCommunication fun

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

  world <- get
  case cmtRange world of
    Just _ -> do
      -- add randomCommitment transactions
      addRandomCmtTrans modifyModule

      -- add openCommitment for ADV
      addAdvOpenCmtTrans modifyModule
    Nothing ->
      return ()
  
  case sigType world of
    Just _ -> do
      -- aad updateSignature for ADV
      addAdvUpdateSignatureTranss modifyModule
    Nothing ->
      return ()

  -- add critical sections stuff 
  _ <- modifyModule addCS2

  --------------------------------------------
  -- Extra transs added manually without CS --
  --------------------------------------------

  case cmtRange world of
    Just _ -> do
      -- add openCommitment transactions without commstate=1 etc.
      addHonestOpenCmtTrans modifyModule
    Nothing ->
      return ()

  case sigType world of
    Just _ -> do
      -- add updateSignature transactions without commstate=1 etc.
      addHonestUpdateSignatureTranss modifyModule
    Nothing ->
      return ()

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

