module WorldPrismEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import AbsEthver
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
  addedGuards :: [Exp]
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
  whichSender :: Ident
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
  addedGuards = []
  } 

emptyModule :: Module
emptyModule = Module {number = nUndefModuleNumber, stateVar = sEmptyState, moduleName = sEmptyModule, 
  vars = Map.empty, varsInitialValues = Map.empty, numLocals = 0, currState = 1, numStates = 1,
  breakStates = [],
  transs = [], whichSender = Ident sEmptySender}


addAutoVars :: VerRes ()
addAutoVars = do
  world <- get

  -- blockchain:

  -- TODO: only 2 players
  addVar modifyBlockchain (TUInt 2) iContrSender
  -- TODO: skąd wziąć zakres value?
  -- ODP: Z (constants world). A tam wczytać z kodu źródłowego
  case Map.lookup iMaxValue (constants world) of
    Nothing -> error $ sMaxValue ++ " constant definition not found in the source file.\n"
    Just maxValue -> addVar modifyBlockchain (TUInt (maxValue + 1)) iValue
  -- TODO: hard-fixed MAX_TIME for 2
  addVar modifyBlockchain (TUInt 3) (Ident sTimeElapsed)
  addInitialValue modifyBlockchain (Ident sTimeElapsed) (EInt 0)

  -- contract:

  case Map.lookup (Ident sMaxContractBalance) $ constants world of
    Just maxContractBalance -> do
      case Map.lookup (Ident sInitContractBalance) (constants world) of
        Just initContractBalance -> do
          addVar modifyContract (TUInt $ maxContractBalance + 1) (Ident sContractBalance)
          addInitialValue modifyContract (Ident sContractBalance) (EInt initContractBalance)
        _ -> error $ sInitContractBalance ++ "not found in (constants world)"
    _ -> error $ sMaxContractBalance ++ " not found in (constants world)"
  
  -- scenarios
  {-addVar modifyPlayer0 TBool (Ident $ sWaits ++ "0")
  addInitialValue modifyPlayer0 (Ident $ sWaits ++ "0") EFalse

  addVar modifyPlayer1 TBool (Ident $ sWaits ++ "1")
  addInitialValue modifyPlayer1 (Ident $ sWaits ++ "1") EFalse
  -}
  -- TODO: move rest of variables from contractPream etc. to here.

  -- communication:
  
  -- TODO: only 2 players
  addVar modifyCommunication (TUInt 2) iCommSender

------------------------
-- WORLD MODIFICATION --
------------------------

addProps :: String -> VerRes ()
addProps text = do
  world <- get
  put (world {props = (props world) ++ text})

addFun :: Function -> VerRes ()
addFun (Fun name args stms) = do
  world <- get
  put $ world {funs = Map.insert name (Fun name args stms) $ funs world}
  
addFun (FunR name args typ stms) = do
  world <- get
  put $ world {funs = Map.insert name (FunR name args typ stms) $ funs world}

addContractFun :: Function -> VerRes ()
addContractFun (Fun name args stms) = do
  world <- get
  put $ world {contractFuns = Map.insert name (Fun name args stms) $ contractFuns world}
  
addContractFun (FunR name args typ stms) = do
  world <- get
  put $ world {contractFuns = Map.insert name (FunR name args typ stms) $ contractFuns world}

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
  _ <- modifyModule (addVarToModule typ ident)
  return ()

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

-- TODO: adds function name as a prefix of a variable name
createScenarioArgumentName :: Ident -> Ident -> Integer -> Ident
createScenarioArgumentName (Ident funName) (Ident varName) playerName = 
    --Ident $ funName ++ "_" ++ varName ++ (show playerName)
    Ident $ varName ++ (show playerName)

-- TODO: does not add function name as a prefix
createCoArgumentName :: Ident -> Ident -> Ident
createCoArgumentName (Ident funName) (Ident varName) = 
    Ident $ varName

-- TODO: with prefix or not? Now: funName ignored
addNoPlayerArg :: ModifyModuleType -> Ident -> Arg -> VerRes ()
addNoPlayerArg modifyModule (Ident funName) (Ar typ varName) = do
  addVar modifyModule typ varName

-- TODO: with prefix of not?
addPlayerArg :: ModifyModuleType -> Ident -> Arg -> VerRes ()
addPlayerArg modifyModule funName (Ar typ varName) = do
  mod <- modifyModule id
  addVar modifyModule typ $ createScenarioArgumentName funName varName (number mod)

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

-- TODO: stos dla zagnieżdżonych wywołań?
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

addLazyRandom :: Ident -> VerRes ()
addLazyRandom ident = do
  world <- get
  put $ world {lazyRandoms = Set.insert ident $ lazyRandoms world}

removeLazyRandom :: Ident -> VerRes ()
removeLazyRandom ident = do
  world <- get
  put $ world {lazyRandoms = Set.delete ident $ lazyRandoms world}

-- default values
defaultValueOfType :: Type -> Exp
defaultValueOfType TBool = EFalse
defaultValueOfType (TRUInt _) = EInt 0
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

