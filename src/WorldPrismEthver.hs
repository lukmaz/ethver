module WorldPrismEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import AbsEthver
import AuxEthver
import AuxPrismEthver
import ConstantsEthver

-- TYPES --

type VerRes a = State VerWorld a
type Trans = (String, [Exp], [Branch])
type ModifyModuleType = (Module -> Module) -> VerRes Module

data Liveness = Alive | Dead

type Branch = ([(Ident, Exp)], [Liveness])

instance Show Liveness where
  show Alive = "Alive"
  show Dead = "Dead"

instance Eq Liveness where
  Dead == Dead = True
  Alive == Alive = True
  Dead == Alive = False
  Alive == Dead = False

data VerWorld = VerWorld {
  props :: String,
  funs :: Map.Map Ident Function,
  contractFuns :: Map.Map Ident Function,
  constants :: Map.Map Ident Integer,
  playerNumbers :: Map.Map String Integer,
  returnVar :: [Ident],
  blockchain :: Module,
  contract :: Module,
  communication :: Module,
  player0 :: Module,
  player1 :: Module,
  condVars :: Set.Set Ident,
  -- set of indexes which are read in condition checks (ESender or EInt) - AND ALSO EVar! (TODO?)
  condArrays :: Map.Map Ident (Set.Set Exp),
  varsValues :: Map.Map Ident Exp,
  -- map (arrayName, index) -> value
  arraysValues :: Map.Map (Ident, Exp) Exp,
  condRandoms :: Set.Set Ident,
  -- set of indexes which are read in condition checks (ESender or EInt) - AND ALSO EVar! (TODO?)
  condRandomArrays :: Map.Map Ident (Set.Set Exp),
  lazyRandoms :: Set.Set Ident,
  addedGuards :: [Exp],
  senderNumber :: Maybe Integer,
  cmtRange :: Maybe Integer,
  sigType :: Maybe Type
  }

data Module = Module {
  number :: Integer,
  stateVar :: String,
  moduleName :: String,
  vars :: Map.Map Ident Type,
  varsInitialValues :: Map.Map Ident Exp,
  numLocals :: Integer,
  currState :: Integer,
  numStates :: Integer,
  breakStates :: [Integer],
  transs :: [Trans],
  whichSender :: Ident,
  globalCommitments :: Map.Map Ident Type,
  globalSignatures :: Map.Map Ident Type
  }
  


-- INITIALIZATION --

emptyVerWorld :: VerWorld
emptyVerWorld = VerWorld {
  props = "", 
  funs = Map.empty,
  contractFuns = Map.empty,
  constants = Map.empty,
  playerNumbers = Map.empty, 
  returnVar = [], 
  blockchain = emptyModule {stateVar = sBCState, moduleName = sBCModule, whichSender = iContrSender}, 
  contract = emptyModule {stateVar = sContrState, moduleName = sContrModule, whichSender = iContrSender}, 
  communication = emptyModule {stateVar = sCommState, moduleName = sCommModule, whichSender = iCommSender},
  player0 = emptyModule {number = 0, stateVar = sP0State, moduleName = sP0Module}, 
  player1 = emptyModule {number = 1, stateVar = sP1State, moduleName = sP1Module},
  condVars = Set.empty,
  varsValues = Map.empty,
  arraysValues = Map.empty,
  condArrays = Map.empty,
  condRandoms = Set.empty,
  condRandomArrays = Map.empty,
  lazyRandoms = Set.empty,
  addedGuards = [],
  senderNumber = Nothing,
  cmtRange = Nothing,
  sigType = Nothing
  } 

emptyModule :: Module
emptyModule = Module {number = nUndefModuleNumber, stateVar = sEmptyState, moduleName = sEmptyModule, 
  vars = Map.empty, varsInitialValues = Map.empty, numLocals = 0, currState = 1, numStates = 1,
  breakStates = [],
  transs = [], whichSender = Ident sEmptySender,
  globalCommitments = Map.empty,
  globalSignatures = Map.empty
  }


addAutoVars :: VerRes ()
addAutoVars = do
  world <- get

  -- blockchain:

  addVar modifyBlockchain (TUInt 2) iContrSender
  case Map.lookup iMaxValue (constants world) of
    Nothing -> error $ sMaxValue ++ " constant definition not found in the source file.\n"
    Just maxValue -> do
      addVar modifyBlockchain (TUInt (maxValue + 1)) iValue

  -- contract:

  case Map.lookup (Ident sMaxContractBalance) $ constants world of
    Just maxContractBalance -> do
      case Map.lookup (Ident sInitContractBalance) (constants world) of
        Just initContractBalance -> do
          addVar modifyContract (TUInt $ maxContractBalance + 1) (Ident sContractBalance)
          addInitialValue modifyContract (Ident sContractBalance) (EInt initContractBalance)
        _ -> error $ sInitContractBalance ++ "not found in (constants world)"
    _ -> error $ sMaxContractBalance ++ " not found in (constants world)"
  

  -- communication:
  
  addVar modifyCommunication (TUInt 2) iCommSender

------------------------
-- WORLD MODIFICATION --
------------------------

addProps :: String -> VerRes ()
addProps text = do
  world <- get
  put (world {props = (props world) ++ text})

addFun :: Function -> VerRes ()
addFun fun = do
  world <- get
  put $ world {funs = Map.insert (getFunName fun) fun $ funs world}
  
addContractFun :: Function -> VerRes ()
addContractFun fun = do
  world <- get
  put $ world {contractFuns = Map.insert (getFunName fun) fun $ contractFuns world}
  
addConstant :: ConstantDecl -> VerRes ()
addConstant (Const ident value) = do
  world <- get
  put $ world {constants = Map.insert ident value $ constants world}

addLocal :: ModifyModuleType -> Type -> VerRes ()
addLocal modifyModule typ = do
  mod <- modifyModule id
  let varName = (moduleName mod) ++ sLocalSuffix ++ (show $ numLocals mod)
  addVar modifyModule typ (Ident varName)
  _ <- modifyModule (\mod -> mod {numLocals = numLocals mod + 1})
  return ()

-- General addVar
addVar :: ModifyModuleType -> Type -> Ident -> VerRes ()
addVar modifyModule typ ident = do
  case typ of
    TCUInt range -> do
      addCmtIdVar modifyModule ident 
    _ -> do
      _ <- modifyModule (addVarToModule typ ident)
      return ()

addSigIdVar :: ModifyModuleType -> Type -> Ident -> VerRes ()
addSigIdVar modifyModule typ varIdent = do
  addVar modifyModule typ varIdent

addCmtIdVar :: ModifyModuleType -> Ident -> VerRes ()
addCmtIdVar modifyModule varIdent = do
  addVar modifyModule (TUInt nMaxCommitments) varIdent
  
addInitialValue :: ModifyModuleType -> Ident -> Exp -> VerRes ()
addInitialValue modifyModule ident exp = do
  _ <- modifyModule (addInitialValueToModule ident exp)
  return ()

-- cond variables
addCondVar :: Ident -> VerRes ()
addCondVar ident = do
  world <- get
  put (world {condVars = Set.insert ident (condVars world)})

addCondArrays :: Ident -> Exp -> VerRes ()
addCondArrays varName index = do
  world <- get
  let arrays = condArrays world
  case Map.lookup varName arrays of
    Nothing -> do
      put $ world {condArrays = Map.insert varName (Set.singleton index) arrays}
    Just s -> do
      put $ world {condArrays = Map.insert varName (Set.insert index s) arrays}
     

addCondRandom :: Ident -> VerRes ()
addCondRandom varName = do
  world <- get
  put $ world {condRandoms = Set.insert varName $ condRandoms world}

addCondRandomArray :: Ident -> Exp -> VerRes ()
addCondRandomArray varName index = do
  world <- get
  let arrays = condRandomArrays world
  case Map.lookup varName arrays of
    Nothing -> do
      put $ world {condRandomArrays = Map.insert varName (Set.singleton index) arrays}
    Just s -> do
      put $ world {condRandomArrays = Map.insert varName (Set.insert index s) arrays}

clearCondVarsAndArrays :: VerRes ()
clearCondVarsAndArrays = do
  world <- get
  put (world {condVars = Set.empty, condArrays = Map.empty})

clearCondRandoms :: VerRes ()
clearCondRandoms = do
  world <- get
  put (world {condRandoms = Set.empty, condRandomArrays = Map.empty, lazyRandoms = Set.empty})

-- adds function name as a prefix of a variable name
createScenarioArgumentName :: String -> Ident -> Ident -> Integer -> Ident
createScenarioArgumentName suffix (Ident funName) (Ident varName) playerName = 
    Ident $ varName ++ (show playerName) ++ suffix

-- does not add function name as a prefix
createCoArgumentName :: String -> Ident -> Ident -> Ident
createCoArgumentName suffix (Ident funName) (Ident varName) = 
    Ident $ varName ++ suffix

addNoPlayerArg :: ModifyModuleType -> Ident -> Arg -> VerRes ()
addNoPlayerArg modifyModule (Ident funName) (Ar (TCUInt range) varIdent) = do
  addCmtIdVar modifyModule varIdent
  addGlobalCommitments range

addNoPlayerArg modifyModule (Ident funName) (Ar (TSig sigTypes) varIdent) = do
  addSigIdVar modifyModule (TSig sigTypes) varIdent
  addGlobalSignatures (TSig sigTypes)

addNoPlayerArg modifyModule (Ident funName) (Ar typ varIdent) = do
  addVar modifyModule typ varIdent

addPlayerArg :: ModifyModuleType -> Ident -> Arg -> VerRes ()
addPlayerArg modifyModule funName (Ar (TCUInt range) varIdent) = do
  mod <- modifyModule id
  let
    numberedName = createScenarioArgumentName "" funName varIdent (number mod)
  addCmtIdVar modifyModule numberedName
  addGlobalCommitments range

addPlayerArg modifyModule funName (Ar (TSig sigTypes) varIdent) = do
  mod <- modifyModule id
  let
    numberedName = createScenarioArgumentName "" funName varIdent (number mod)
  addSigIdVar modifyModule (TSig sigTypes) numberedName
  addGlobalSignatures (TSig sigTypes)

addPlayerArg modifyModule funName (Ar typ varIdent) = do
  mod <- modifyModule id
  addVar modifyModule typ $ createScenarioArgumentName "" funName varIdent (number mod)

addContrArgument :: Ident -> Arg -> VerRes ()
addContrArgument funName arg = do
  addNoPlayerArg modifyBlockchain funName arg
  addPlayerArg modifyPlayer0 funName arg
  addPlayerArg modifyPlayer1 funName arg

addCommArgument :: Ident -> Arg -> VerRes ()
addCommArgument funName arg = do
  addNoPlayerArg modifyCommunication funName arg
  addPlayerArg modifyPlayer0 funName arg
  addPlayerArg modifyPlayer1 funName arg

-- Players

addPlayer :: String -> VerRes ()
addPlayer str = do
  world <- get
  case Map.lookup str $ playerNumbers world of
    Nothing -> do
      let size = Map.size $ playerNumbers world
      put (world {playerNumbers = Map.insert str (fromIntegral size) $ playerNumbers world})
    Just _ -> return ()

getPlayerNumber :: String -> VerRes Integer
getPlayerNumber str = do
  world <- get
  case Map.lookup str $ playerNumbers world of
    Just number -> return number

deducePlayerNumber :: ModifyModuleType -> VerRes Integer
deducePlayerNumber modifyModule = do
  world <- get
  mod <- modifyModule id

  return $ case senderNumber world of
    Just n -> n
    Nothing ->
      if number mod == nUndefModuleNumber
        then error $ "Cannot determine the player number"
        else number mod
 
addReturnVar :: Ident -> VerRes ()
addReturnVar ident = do
  world <- get
  put (world {returnVar = (ident:(returnVar world))})

removeReturnVar :: VerRes ()
removeReturnVar = do
  world <- get
  put (world {returnVar = tail $ returnVar world})

addGuard :: Exp -> VerRes ()
addGuard exp = do
  world <- get
  put $ world {addedGuards = (exp:(addedGuards world))}

clearAddedGuards :: VerRes ()
clearAddedGuards = do
  world <- get
  put $ world {addedGuards = []}

clearVarsValues :: VerRes ()
clearVarsValues = do
  world <- get
  put $ world {varsValues = Map.empty}

addMultipleVarsValues :: [Ident] -> [Exp] -> VerRes ()
addMultipleVarsValues idents vals = do
  mapM_
    (\(ident, exp) -> assignVarValue ident exp)
    (zip idents vals)

assignVarValue :: Ident -> Exp -> VerRes ()
assignVarValue ident exp = do
  world <- get
  put (world {varsValues = Map.insert ident exp $ varsValues world})

assignArrayValue :: Ident -> Exp -> Exp -> VerRes ()
assignArrayValue ident index value = do
  world <- get
  put (world {arraysValues = Map.insert (ident, index) value $ arraysValues world})

findVarValue :: Ident -> VerRes (Maybe Exp)
findVarValue ident = do
  world <- get
  return $ Map.lookup ident $ varsValues world

findArrayValue :: Ident -> Exp -> VerRes (Maybe Exp)
findArrayValue ident index = do
  world <- get
  return $ Map.lookup (ident, index) $ arraysValues world

-- default values
defaultValueOfType :: Type -> Exp
defaultValueOfType TBool = EFalse
defaultValueOfType (TCUInt x) = EInt (x + 1)
defaultValueOfType (TUInt _) = EInt 0


-------------------------
-- Module modification --
-------------------------

setCurrState :: Integer -> Module -> Module
setCurrState curr mod = 
  mod {currState = curr}

setNumStates :: Integer -> Module -> Module
setNumStates num mod =
  mod {numStates = num}

addBreakState :: Integer -> Module -> Module
addBreakState state mod = 
  mod {breakStates = state:(breakStates mod)}

removeBreakState :: Module -> Module
removeBreakState mod = do
  mod {breakStates = tail $ breakStates mod}

addVarToModule :: Type -> Ident -> Module -> Module
addVarToModule typ ident mod = do
  mod {vars = Map.insert ident typ (vars mod)}

addInitialValueToModule :: Ident -> Exp -> Module -> Module
addInitialValueToModule ident exp mod = do
  mod {varsInitialValues = Map.insert ident exp (varsInitialValues mod)}

modifyBlockchain :: (Module -> Module) -> VerRes Module
modifyBlockchain fun = do
  world <- get
  put (world {blockchain = fun $ blockchain world})
  world <- get
  return $ blockchain world

modifyContract :: (Module -> Module) -> VerRes Module
modifyContract fun = do
  world <- get
  put (world {contract = fun $ contract world})
  world <- get
  return $ contract world

modifyCommunication :: (Module -> Module) -> VerRes Module
modifyCommunication fun = do
  world <- get
  put (world {communication = fun $ communication world})
  world <- get
  return $ communication world

modifyPlayer0 :: (Module -> Module) -> VerRes Module
modifyPlayer0 fun = do
  world <- get
  put (world {player0 = fun $ player0 world})
  world <- get
  return $ player0 world

modifyPlayer1 :: (Module -> Module) -> VerRes Module
modifyPlayer1 fun = do
  world <- get
  put (world {player1 = fun $ player1 world})
  world <- get
  return $ player1 world

-------------------
-- applyToBranch --
-------------------

applyToBranch :: ([(Ident, Exp)] -> [(Ident, Exp)]) -> Branch -> Branch
applyToBranch f (br, liv) = (f br, liv)


-- Trans

addTransToNewState :: ModifyModuleType -> String -> [Exp] -> [Branch] -> VerRes ()
addTransToNewState modifyModule transName guards updates = do
  mod <- modifyModule id
  let newState = numStates mod + 1
  addCustomTrans modifyModule transName (currState mod) newState guards updates
  _ <- modifyModule (setCurrState newState)
  _ <- modifyModule (setNumStates newState)
  return ()

add2TranssToNewState :: ModifyModuleType -> String -> [Exp] -> [Branch] -> String -> [Exp] -> [Branch] -> VerRes ()
add2TranssToNewState modifyModule transName1 guards1 updates1 transName2 guards2 updates2 = do
  mod <- modifyModule id
  let newState = numStates mod + 1

  addCustomTrans
    modifyModule
    transName1
    (currState mod)
    newState
    guards1
    updates1

  addCustomTrans
    modifyModule
    transName2
    (currState mod)
    newState
    guards2
    updates2

  _ <- modifyModule (setCurrState newState)
  _ <- modifyModule (setNumStates newState)
  return ()

addCustomTrans :: ModifyModuleType -> String -> Integer -> Integer -> [Exp] -> [Branch] -> VerRes ()
addCustomTrans modifyModule transName fromState toState guards updates = do
  mod <- modifyModule id
  let newTrans = newCustomTrans (stateVar mod) transName fromState toState guards updates
  _ <- modifyModule (addTransToModule newTrans)
  return ()

addFirstCustomTrans :: ModifyModuleType -> String -> Integer -> Integer -> [Exp] -> [Branch] -> VerRes ()
addFirstCustomTrans modifyModule transName fromState toState guards updates = do
  mod <- modifyModule id
  let newTrans = newCustomTrans (stateVar mod) transName fromState toState guards updates
  _ <- modifyModule (addFirstTransToModule newTrans)
  return ()


addTransNoState :: ModifyModuleType -> String -> [Exp] -> [Branch] -> VerRes ()
addTransNoState modifyModule transName guards updates = do
  mod <- modifyModule id
  let newTrans = newTransNoState transName guards updates
  _ <- modifyModule (addTransToModule newTrans)
  return ()

newCustomTrans :: String -> String -> Integer -> Integer -> [Exp] -> [Branch] -> Trans
newCustomTrans stateVar transName fromState toState guards updates =
  newTransNoState
    transName
    ((EEq (EVar (Ident stateVar)) (EInt fromState)):guards)
    (map (applyToBranch ((Ident stateVar, EInt toState):)) updates)
  

newTransNoState :: String -> [Exp] -> [Branch] -> Trans
newTransNoState transName guards updates =
  (transName, guards, updates)

addTransToModule :: Trans -> Module -> Module
addTransToModule tr mod = 
  mod {transs = tr:(transs mod)}

addFirstTransToModule :: Trans -> Module -> Module
addFirstTransToModule tr mod =
  mod {transs = (transs mod) ++ [tr]}

-----------------
-- Commitments --
-----------------

setCmtRange :: Integer -> VerRes ()
setCmtRange range = do
  world <- get
  case cmtRange world of
    Nothing ->
      put $ world {cmtRange = Just range}
    Just old_range -> do
      if old_range /= range
        then error $ "Commitment range changed"
        else return ()

addAdvOpenCmtTrans :: ModifyModuleType -> VerRes ()
addAdvOpenCmtTrans modifyModule = do
  mod <- modifyModule id
  world <- get
  let 
    nr = show $ number mod
    cmtIdent = Ident $ sGlobalCommitments ++ "_" ++ nr
  
  case cmtRange world of
    Just range -> do 
      -- committed -> random (adv, no sync)
      addCustomTrans
        modifyModule
        ""
        (-1)
        (-1)
        [EEq (EVar cmtIdent) (EInt range)]
        (foldl
          (\acc x -> acc ++ [([(cmtIdent, EInt x)], [Alive])])
          []
          [0..(range - 1)]
        )
      
      -- not committed -> chosen (adv, no sync)
      mapM_ 
        (\nr -> addCustomTrans
          modifyModule
          ""
          (-1)
          (-1)
          [EEq (EVar cmtIdent) (EInt $ range + 1)]
          [([(cmtIdent, EInt nr)], [Alive])]
        )
        [0..(range - 1)]
    _ ->
      error $ "Commitment range not set at the moment of adding adversarial opening the commitment"

addRandomCmtTrans :: ModifyModuleType -> VerRes ()
addRandomCmtTrans modifyModule = do
  mod <- modifyModule id
  world <- get
  let 
    nr = show $ number mod
    cmtIdent = Ident $ sGlobalCommitments ++ "_" ++ nr
  
  case cmtRange world of
    Just range -> do 
      -- not committed -> committed
      addCustomTrans
        modifyModule
        ""
        (-1)
        (-1)
        [EEq (EVar cmtIdent) (EInt $ range + 1)]
        [([(cmtIdent, EInt range)], [Alive])]
    _ ->
      error $ "Commitment range not set at the moment of adding adversarial opening the commitment"

----------------
-- Signatures --
----------------

setSigType :: Type -> VerRes ()
setSigType typ = do
  world <- get
  case sigType world of
    Nothing ->
      put $ world {sigType = Just typ}
    Just old_typ -> do
      if old_typ /= typ
        then error $ "Signature type changed"
        else return ()


addGlobalCommitments :: Integer -> VerRes ()
addGlobalCommitments range = do
  let 
    ident0 = Ident $ sGlobalCommitments ++ "_0"
    ident1 = Ident $ sGlobalCommitments ++ "_1"
    typ = TCUInt range
  _ <- modifyPlayer0 (\p -> p {globalCommitments = Map.fromList [(ident0, typ)]})
  _ <- modifyPlayer1 (\p -> p {globalCommitments = Map.fromList [(ident1, typ)]})
  setCmtRange range
  return ()

addGlobalSignatures :: Type -> VerRes ()
addGlobalSignatures typ = do
  let
    ident0 = Ident $ sGlobalSignatures ++ "_0"
    ident1 = Ident $ sGlobalSignatures ++ "_1"
    identComm = Ident $ sCommSignature 
  _ <- modifyPlayer0 (\p -> p {globalSignatures = Map.fromList [(ident0, typ)]})
  _ <- modifyPlayer1 (\p -> p {globalSignatures = Map.fromList [(ident1, typ)]})
  _ <- modifyCommunication (\p -> p {globalSignatures = Map.fromList [(identComm, typ)]})
  setSigType typ
  return ()

