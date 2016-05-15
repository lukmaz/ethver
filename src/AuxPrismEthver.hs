module AuxPrismEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map

import AbsEthver
import ErrM


-- TYPES --

type VerRes a = State VerWorld a
type Trans = (String, [Exp], [[(Ident, Exp)]])
type ModifyModuleType = (Module -> Module) -> VerRes Module

data VerWorld = VerWorld {
  props :: String,
  funs :: Map.Map Ident Function,
  argMap :: Map.Map Ident Ident,
  playerNumbers :: Map.Map String Integer,
  returnVar :: [Ident],
  blockchain :: Module,
  contract :: Module,
  player0 :: Module,
  player1 :: Module
  }

data Module = Module {
  number :: Integer,
  stateVar :: String,
  vars :: Map.Map Ident Type,
  numLocals :: Integer,
  currState :: Integer,
  numStates :: Integer,
  transs :: [Trans]
  }
  


-- INITIALIZATION --

emptyVerWorld :: VerWorld
emptyVerWorld = VerWorld {
  props = "", 
  funs = Map.empty,
  argMap = Map.empty,
  playerNumbers = Map.empty, 
  returnVar = [], 
  blockchain = emptyModule {stateVar = "bcstate"}, 
  contract = emptyModule {stateVar = "cstate"}, 
  player0 = emptyModule {number = 0, stateVar = "state0"}, 
  player1 = emptyModule {number = 1, stateVar = "state1"}
  } 

emptyModule :: Module
emptyModule = Module {number = 42, stateVar = "emptyState", vars = Map.empty, numLocals = 0,
  currState = 1, numStates = 1, transs = []}

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
  
-- TODO: czy te 4 funkcje są potrzebne?
addBcVar :: Type -> Ident -> VerRes ()
addBcVar = addVar modifyBlockchain

addContrVar :: Type -> Ident -> VerRes ()
addContrVar = addVar modifyContract

addP0Var :: Type -> Ident -> VerRes ()
addP0Var = addVar modifyPlayer0

addP1Var :: Type -> Ident -> VerRes ()
addP1Var = addVar modifyPlayer1

addLocal :: ModifyModuleType -> Type -> VerRes ()
addLocal modifyModule typ = do
  mod <- modifyModule id
  let varName = "local" ++ (show $ numLocals mod)
  addVar modifyModule typ (Ident varName)
  _ <- modifyModule (\mod -> mod {numLocals = numLocals mod + 1})
  return ()

-- General addVar
addVar :: ModifyModuleType -> Type -> Ident -> VerRes ()
addVar modifyModule typ ident = do
  _ <- modifyModule (addVarToModule typ ident)
  return ()

addBcArg :: ModifyModuleType -> Ident -> Arg -> VerRes ()
addBcArg modifyModule (Ident funName) (Ar typ (Ident varName)) = do
  addVar modifyModule typ (Ident $ funName ++ "_" ++ varName)

addPlayerArg :: ModifyModuleType -> Ident -> Arg -> VerRes ()
addPlayerArg modifyModule (Ident funName) (Ar typ (Ident varName)) = do
  mod <- modifyModule id
  addVar modifyModule typ (Ident $ funName ++ "_" ++ varName ++ (show $ number mod))

addArgToMap :: Ident -> Arg -> VerRes ()
addArgToMap (Ident funName) (Ar _ (Ident varName)) = do
  world <- get
  put (world {argMap = Map.insert (Ident varName) (Ident $ funName ++ "_" ++ varName) $ argMap world})
  
clearArgMap :: VerRes ()
clearArgMap = do
  world <- get
  put (world {argMap = Map.empty})

addArgument :: Ident -> Arg -> VerRes ()
addArgument funName arg = do
  addBcArg modifyBlockchain funName arg
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


-----------
-- Trans --
-----------

addTransToNewState :: ModifyModuleType -> String -> [Exp] -> [[(Ident, Exp)]] -> VerRes ()
addTransToNewState modifyModule transName guards updates = do
  mod <- modifyModule id
  let newState = numStates mod + 1
  addCustomTrans modifyModule transName (currState mod) newState guards updates
  _ <- modifyModule (setCurrState newState)
  _ <- modifyModule (setNumStates newState)
  return ()

addCustomTrans :: ModifyModuleType -> String -> Integer -> Integer -> [Exp] -> [[(Ident, Exp)]] -> VerRes ()
addCustomTrans modifyModule transName fromState toState guards updates = do
  mod <- modifyModule id
  let newTrans = newCustomTrans (stateVar mod) transName fromState toState guards updates
  _ <- modifyModule (addTransToModule newTrans)
  return ()

addFirstCustomTrans :: ModifyModuleType -> String -> Integer -> Integer -> [Exp] -> [[(Ident, Exp)]] -> VerRes ()
addFirstCustomTrans modifyModule transName fromState toState guards updates = do
  mod <- modifyModule id
  let newTrans = newCustomTrans (stateVar mod) transName fromState toState guards updates
  _ <- modifyModule (addFirstTransToModule newTrans)
  return ()


addTransNoState :: ModifyModuleType -> String -> [Exp] -> [[(Ident, Exp)]] -> VerRes ()
addTransNoState modifyModule transName guards updates = do
  mod <- modifyModule id
  let newTrans = newTransNoState transName guards updates
  _ <- modifyModule (addTransToModule newTrans)
  return ()

newCustomTrans :: String -> String -> Integer -> Integer -> [Exp] -> [[(Ident, Exp)]] -> Trans
newCustomTrans stateVar transName fromState toState guards updates =
  newTransNoState
    transName
    ((EEq (EVar (Ident stateVar)) (EInt fromState)):guards)
    (map ((Ident stateVar, EInt toState):) updates)
  

newTransNoState :: String -> [Exp] -> [[(Ident, Exp)]] -> Trans
newTransNoState transName guards updates =
  (transName, guards, updates)

addTransToModule :: Trans -> Module -> Module
addTransToModule tr mod = 
  mod {transs = tr:(transs mod)}

addFirstTransToModule :: Trans -> Module -> Module
addFirstTransToModule tr mod =
  mod {transs = (transs mod) ++ [tr]}

----------------------
-- Critical section --
----------------------

-- converts all commands in a module by adding critical section stuff
addCS :: Module -> Module
addCS mod = 
  mod { transs = reverse $ 
    foldl
      (\acc tr -> ((setCS (number mod) tr):(unsetCS (number mod) tr):acc))
      []
      (transs mod)
  }
  
setCS :: Integer -> Trans -> Trans
setCS number (_, guards, _) = 
  (
    "",
    (ENot $ EVar $ Ident "critical_section0")
      :(ENot $ EVar $ Ident "critical_section1")
      :(head guards)
      :(drop 2 guards),
    [[(Ident $ "critical_section" ++ (show number), ETrue)]]
  )

unsetCS :: Integer -> Trans -> Trans
unsetCS number (transName, guards, updates) =
  (
    transName,
    (EVar $ Ident $ "critical_section" ++ (show number))
      :guards,
    (map ((Ident $ "critical_section" ++ (show number), EFalse):) updates)
  )

---------------------
-- MONEY TRANSFERS --
---------------------

transferFromContract :: Ident -> Exp -> VerRes ()
transferFromContract to value = do
  transferMoney (Ident "contract_balance") to (EVar (Ident "MAX_USER_BALANCE")) value
  

transferMoney :: Ident -> Ident -> Exp -> Exp -> VerRes ()
transferMoney from to maxTo value = do
  addTransToNewState
    --TODO: czy to przypadkiem nie ma być w BC?
    modifyContract
    ""
    [EGe (EVar from) value, ELe (EAdd (EVar to) value) maxTo]
    [[(from, ESub (EVar from) value), (to, EAdd (EVar to) value)]]

--------------------------------
-- CODE GENERATION FROM WORLD --
--------------------------------

-- generates PRISM model code from VerWorld
generatePrism :: VerWorld -> String
generatePrism world = 
  "mdp\n\n" ++
  "const int ADVERSARY;\n\n" ++ 
  generateConstants ++
  (generateNumStates world) ++
  (generateMaxBalances) ++ 
  (generateModule blockchain "blockchain" blockchainPream world) ++
  (generateModule contract "contract" contractPream world) ++
  (generateModule player0 "player0" player0Pream world) ++
  (generateModule player1 "player1" player1Pream world)

generateModule :: (VerWorld -> Module) -> String -> String ->VerWorld -> String
generateModule moduleFun moduleName pream world = 
  "\n\n/////////////////////\n" ++
  "\nmodule " ++ moduleName ++ "\n" ++
  pream ++ "\n" ++
  (prismVars $ vars $ moduleFun world) ++
  "\n" ++ 
  prismTranss (reverse $ transs $ moduleFun world) ++
  "endmodule\n\n\n"

blockchainPream :: String
blockchainPream =
  "  sender : [0..1];\n" ++
  -- TODO: skąd wziąć zakres val?
  "  val : [0..2];\n"

contractPream :: String
contractPream =
  "  cstate : [0..NUM_CONTRACT_STATES] init 1;\n" ++
  "  next_state : [0..NUM_CONTRACT_STATES];\n" ++
  "  contract_balance : [0..MAX_CONTRACT_BALANCE];\n" ++
  -- TODO: skąd wziąć zakresy balance?
  "  balance0 : [0..MAX_USER_BALANCE] init 2;\n" ++
  "  balance1 : [0..MAX_USER_BALANCE] init 0;\n"

player0Pream :: String
player0Pream =
  "  state0 : [-1..NUM_PLAYER0_STATES] init 0;\n" ++
  "  critical_section0 : bool;\n"

player1Pream :: String
player1Pream =
  "  state1 : [-1..NUM_PLAYER1_STATES] init 0;\n" ++
  "  critical_section1 : bool;\n"

generateConstants :: String
generateConstants = 
  "const int T_NONE = 0;\n" ++
  "const int T_BROADCAST = 1;\n" ++
  "const int T_EXECUTED = 2;\n" ++
  "const int T_INVALIDATED = 3;\n\n"

generateNumStates :: VerWorld -> String
generateNumStates world = 
  "const int NUM_CONTRACT_STATES = " ++
  (show $ numStates $ contract world) ++
  ";\n" ++
  "const int NUM_PLAYER0_STATES = " ++
  (show $ numStates $ player0 world) ++
  ";\n" ++
  "const int NUM_PLAYER1_STATES = " ++
  (show $ numStates $ player1 world) ++
  ";\n\n"

-- TODO: skąd?
generateMaxBalances :: String
generateMaxBalances =
  "const int MAX_CONTRACT_BALANCE = 4;\n" ++
  "const int MAX_USER_BALANCE = 4;\n\n"

prismVars :: Map.Map Ident Type -> String
prismVars vars = 
  Map.foldlWithKey
    (\code ident typ -> code ++ "  " ++ (prismShowIdent ident)
      ++ " : " ++ (prismShowType typ) ++ ";\n")
    "" 
    vars

-----------------
-- prism Trans --
-----------------

-- generates PRISM code for all the transitions
prismTranss :: [Trans] -> String
prismTranss transs =
  foldl 
    (\acc trans -> acc ++ (prismTrans trans) ++ "\n")
    "" 
    transs
  
prismTrans :: Trans -> String
prismTrans (transName, guards, updates) =
  "  [" ++ transName ++ "]\n    " ++ (prismGuards guards) ++ "  ->\n" ++ prismUpdates updates ++ ";\n"

prismGuards :: [Exp] -> String
prismGuards [] = ""

prismGuards (h:t) = 
  "(" ++ prismShowExp h ++ ")\n" ++
    foldl 
      (\acc exp -> acc ++ "  & (" ++ (prismShowExp exp) ++ ")\n")
      ""
      t

prismUpdates :: [[(Ident, Exp)]] -> String
prismUpdates [] = ""

prismUpdates [updates] = 
  "    " ++ prismUpdatesDeterm updates

prismUpdates (h:t) = 
  let n = length (h:t) in
    foldl
      (\acc updates -> acc ++ " +\n    1/" ++ (show n) ++ ": " ++
        (prismUpdatesDeterm updates))
      ("    1/" ++ (show n) ++ ": " ++ (prismUpdatesDeterm h))
      t

prismUpdatesDeterm :: [(Ident, Exp)] -> String
prismUpdatesDeterm (h:t) = 
  (prismUpdate h) ++
    foldl
      (\acc update -> acc ++ "\n  & " ++ (prismUpdate update))
      ""
      t

prismUpdate :: (Ident, Exp) -> String
prismUpdate (ident, exp) =
  "(" ++ (prismShowIdent ident) ++ "' = " ++ (prismShowExp exp) ++ ")"


-- PRISM SHOW --

prismShowType :: Type -> String
prismShowType (TUInt x) = "[0.." ++ (show $ x - 1) ++ "]" 
prismShowType (TRUInt x) = "[0.." ++ (show x) ++ "]"
prismShowType TBool = "bool"

prismShowIdent :: Ident -> String
prismShowIdent (Ident ident) = ident

-- TODO: porównanie w ver jest =, a w sol jest ==. Ale chyba będą i tak dwie różne
-- funkcje w CompilerEth i CompilerPrism. Wspólny chcemy mieć tylko typ Exp.
prismShowExp :: Exp -> String

prismShowExp (EEq e1 e2) = 
  prismShowExp e1 ++ " = " ++ prismShowExp e2

prismShowExp (ENe e1 e2) = 
  prismShowExp e1 ++ " != " ++ prismShowExp e2

prismShowExp (EGt e1 e2) = 
  prismShowExp e1 ++ " > " ++ prismShowExp e2

prismShowExp (EGe e1 e2) = 
  prismShowExp e1 ++ " >= " ++ prismShowExp e2

prismShowExp (ELt e1 e2) = 
  prismShowExp e1 ++ " < " ++ prismShowExp e2

prismShowExp (ELe e1 e2) = 
  prismShowExp e1 ++ " <= " ++ prismShowExp e2

prismShowExp (EAdd e1 e2) =
  prismShowExp e1 ++ " + " ++ prismShowExp e2

prismShowExp (ESub e1 e2) =
  prismShowExp e1 ++ " - " ++ prismShowExp e2

prismShowExp (EMul e1 e2) =
  prismShowExp e1 ++ " * " ++ prismShowExp e2

prismShowExp (EDiv e1 e2) =
  "floor(" ++ prismShowExp e1 ++ " / " ++ prismShowExp e2 ++ ")"

prismShowExp (EMod e1 e2) =
  "mod(" ++ prismShowExp e1 ++ ", " ++ prismShowExp e2 ++ ")"

prismShowExp (ENot e1) =
  "!" ++ prismShowExp e1

prismShowExp (ENeg e1) =
  "-" ++ prismShowExp e1

-- TODO: szukać dokładniej, jeśli nazwy lok/glob się przekrywają
prismShowExp (EVar ident) =
  prismShowIdent ident

prismShowExp (EInt x) = 
  show x

prismShowExp (EStr s) =
  s

prismShowExp ESender =
  "sender"

prismShowExp EValue =
  "val"

prismShowExp ETrue = 
  "true"

prismShowExp EFalse = 
  "false"

prismShowExp (ECall (h:t) args) =
  foldl
    (\acc ident -> acc ++ "." ++ (prismShowIdent ident))
    (prismShowIdent h)
    t
  
-- TODO: wszystkie możliwości TOOOOOOODOOOOO


-- minValue, maxValue

findVarType :: Ident -> VerRes (Maybe Type)
findVarType ident = do
  world <- get
  case Map.lookup ident (vars $ blockchain world) of
    Just typ -> return (Just typ)
    Nothing -> 
      case Map.lookup ident (vars $ contract world) of
        Just typ -> return (Just typ)
        Nothing -> 
          case Map.lookup ident (vars $ player0 world) of
            Just typ -> return (Just typ)
            Nothing ->
              case Map.lookup ident (vars $ player1 world) of
                Just typ -> return (Just typ)
                Nothing -> return Nothing

maxRealValueOfType :: Type -> Integer
maxRealValueOfType (TUInt x) = (x - 1)
maxRealValueOfType (TRUInt x) = (x - 1)
maxRealValueOfType TBool = 1

maxTypeValueOfType :: Type -> Integer
maxTypeValueOfType (TUInt x) = (x - 1)
maxTypeValueOfType (TRUInt x) = x
maxTypeValueOfType TBool = 1

minValue :: Ident -> VerRes Integer
minValue ident = do
  typ <- findVarType ident
  case typ of 
    Just (TUInt x) -> return 0
    Just (TRUInt x) -> return 0
    Just TBool -> return 0

maxRealValue :: Ident -> VerRes Integer
maxRealValue ident = do
  typ <- findVarType ident
  case typ of
    Just t -> return $ maxRealValueOfType t

maxTypeValue :: Ident -> VerRes Integer
maxTypeValue ident = do
  typ <- findVarType ident
  case typ of
    Just t -> return $ maxTypeValueOfType t


-- negate cond --
negateExp :: Exp -> Exp
negateExp (EEq e1 e2) = (ENe e1 e2)
negateExp (ENe e1 e2) = (EEq e1 e2)
negateExp (ELt e1 e2) = (EGe e1 e2)
negateExp (ELe e1 e2) = (EGt e1 e2)
negateExp (EGt e1 e2) = (ELe e1 e2)
negateExp (EGe e1 e2) = (ELt e1 e2)

negateExp exp = ENot exp
