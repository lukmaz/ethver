module WorldPrismEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map

import AbsEthver
import ConstantsEthver

-- TYPES --

type VerRes a = State VerWorld a
type Trans = (String, [Exp], [[(Ident, Exp)]])
type ModifyModuleType = (Module -> Module) -> VerRes Module

data VerWorld = VerWorld {
  props :: String,
  funs :: Map.Map Ident Function,
  contractFuns :: Map.Map Ident Function,
  constants :: Map.Map Ident Integer,
  argMap :: Map.Map Ident Ident,
  playerNumbers :: Map.Map String Integer,
  returnVar :: [Ident],
  blockchain :: Module,
  contract :: Module,
  communication :: Module,
  player0 :: Module,
  player1 :: Module
  }

data Module = Module {
  number :: Integer,
  stateVar :: String,
  moduleName :: String,
  vars :: Map.Map Ident Type,
  numLocals :: Integer,
  currState :: Integer,
  numStates :: Integer,
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
  argMap = Map.empty,
  playerNumbers = Map.empty, 
  returnVar = [], 
  blockchain = emptyModule {stateVar = sBCState, moduleName = sBCModule, whichSender = iContrSender}, 
  contract = emptyModule {stateVar = sContrState, moduleName = sContrModule, whichSender = iContrSender}, 
  communication = emptyModule {stateVar = sCommState, moduleName = sCommModule, whichSender = iCommSender},
  player0 = emptyModule {number = 0, stateVar = sP0State, moduleName = sP0Module}, 
  player1 = emptyModule {number = 1, stateVar = sP1State, moduleName = sP1Module}
  } 

emptyModule :: Module
emptyModule = Module {number = nUndefModuleNumber, stateVar = sEmptyState, moduleName = sEmptyModule, 
  vars = Map.empty, numLocals = 0, currState = 1, numStates = 1, transs = [], whichSender = Ident sEmptySender}

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
  let varName = (moduleName mod) ++ sLocalSufix ++ (show $ numLocals mod)
  addVar modifyModule typ (Ident varName)
  _ <- modifyModule (\mod -> mod {numLocals = numLocals mod + 1})
  return ()

-- General addVar
addVar :: ModifyModuleType -> Type -> Ident -> VerRes ()
addVar modifyModule typ ident = do
  _ <- modifyModule (addVarToModule typ ident)
  return ()

addNoPlayerArg :: ModifyModuleType -> Ident -> Arg -> VerRes ()
addNoPlayerArg modifyModule (Ident funName) (Ar typ (Ident varName)) = do
  addVar modifyModule typ (Ident $ funName ++ "_" ++ varName)

addPlayerArg :: ModifyModuleType -> Ident -> Arg -> VerRes ()
addPlayerArg modifyModule (Ident funName) (Ar typ (Ident varName)) = do
  mod <- modifyModule id
  addVar modifyModule typ (Ident $ funName ++ "_" ++ varName ++ (show $ number mod))

-- TODO: co to jest ten argmap?
addArgToMap :: Ident -> Arg -> VerRes ()
addArgToMap (Ident funName) (Ar _ (Ident varName)) = do
  world <- get
  put (world {argMap = Map.insert (Ident varName) (Ident $ funName ++ "_" ++ varName) $ argMap world})
  
clearArgMap :: VerRes ()
clearArgMap = do
  world <- get
  put (world {argMap = Map.empty})

addContrArgument :: Ident -> Arg -> VerRes ()
addContrArgument funName arg = do
  addNoPlayerArg modifyBlockchain funName arg
  addPlayerArg modifyPlayer0 funName arg
  addPlayerArg modifyPlayer1 funName arg
  addArgToMap funName arg

addCommArgument :: Ident -> Arg -> VerRes ()
addCommArgument funName arg = do
  addNoPlayerArg modifyCommunication funName arg
  addPlayerArg modifyPlayer0 funName arg
  addPlayerArg modifyPlayer1 funName arg
  addArgToMap funName arg

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


-------------------------
-- Module modification --
-------------------------

setCurrState :: Integer -> Module -> Module
setCurrState curr mod = 
  mod {currState = curr}

setNumStates :: Integer -> Module -> Module
setNumStates num mod =
  mod {numStates = num}

addVarToModule :: Type -> Ident -> Module -> Module
addVarToModule typ ident mod = do
  mod {vars = Map.insert ident typ (vars mod)}

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

