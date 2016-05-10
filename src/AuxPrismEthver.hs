module AuxPrismEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map

import AbsEthver
import ErrM


-- TYPES --

type VerRes a = State VerWorld a
type Trans = (String, [Exp], [(Ident, Exp)])
type ModifyModuleType = (Module -> Module) -> VerRes Module

data VerWorld = VerWorld {
  props :: String,
  bcVars :: Map.Map Ident Type,
  contrGlobVars :: Map.Map Ident Type,
  contrLocVars :: Map.Map Ident Type,
  p0Vars :: Map.Map Ident Type,
  p1Vars :: Map.Map Ident Type,
  funs :: Map.Map Ident Function,
  addresses :: Map.Map Integer Ident,
  numbers :: Map.Map String Integer,
  returnVar :: [Ident],
  blockchain :: Module,
  contract :: Module,
  player0 :: Module,
  player1 :: Module
  }

data Module = Module {
  stateVar :: String,
  vars :: Map.Map Ident Type,
  currState :: Integer,
  numStates :: Integer,
  transs :: [Trans]
  }
  


-- INITIALIZATION --

emptyVerWorld :: VerWorld
emptyVerWorld = VerWorld {
  props = "", 
  contrGlobVars = Map.empty, 
  bcVars = Map.empty,
  contrLocVars = Map.empty, 
  p0Vars = Map.empty, 
  p1Vars = Map.empty,
  funs = Map.empty, 
  addresses = Map.empty, 
  numbers = Map.empty, 
  returnVar = [], 
  blockchain = emptyModule {stateVar = "bcstate"}, 
  contract = emptyModule {stateVar = "cstate"}, 
  player0 = emptyModule {stateVar = "state0"}, 
  player1 = emptyModule {stateVar = "state1"}
  } 

emptyModule :: Module
emptyModule = Module {stateVar = "emptyState", vars = Map.empty, currState = 1, numStates = 1, transs = []}

-- WORLD MODIFICATION --

addProps :: String -> VerRes ()
addProps text = do
  world <- get
  put (world {props = (props world) ++ text})

addBcVar :: Type -> Ident -> VerRes ()
addBcVar typ ident = do
  world <- get
  put (world {bcVars = Map.insert ident typ (bcVars world)})

addContrGlobVar :: Type -> Ident -> VerRes ()
addContrGlobVar typ ident = do
  world <- get
  put (world {contrGlobVars = Map.insert ident typ (contrGlobVars world)})

addContrLocVar :: Type -> Ident -> VerRes ()
addContrLocVar typ ident = do
  world <- get
  put (world {contrLocVars = Map.insert ident typ (contrLocVars world)})

addP0Var :: Type -> Ident -> VerRes ()
addP0Var typ ident = do
  world <- get
  put (world {p0Vars = Map.insert ident typ (p0Vars world)})

addP1Var :: Type -> Ident -> VerRes ()
addP1Var typ ident = do
  world <- get
  put (world {p1Vars = Map.insert ident typ (p1Vars world)})

-- TODO: ograniczyć deklaracje zmiennych tylko na początek funkcji
-- i tutaj dodać wszystkie deklaracje do loVars
{-addFun :: Function -> VerRes ()
addFun (Fun name args stms) = do
  world <- get
  put (world {funs = Map.insert name (Fun name args stms) (funs world)})

addFun (FunR name args retTyp stms) = do
  addLoVar retTyp (Ident (prismShowIdent name ++ "_retVal"))
  world <- get
  put (world {funs = Map.insert name (FunR name args retTyp stms) (funs world)})
-}

addAddress :: String -> VerRes ()
addAddress str = do
  world <- get
  case Map.lookup str $ numbers world of
    Nothing -> do
      let size = Map.size $ addresses world
      let name = "balance" ++ (show (size + 1))
      put (world {numbers = Map.insert str (fromIntegral (size + 1)) $ numbers world, 
        addresses = Map.insert (fromIntegral (size + 1)) (Ident name) $ addresses world})
    Just _ -> return ()

getAddressNumber :: String -> VerRes Integer
getAddressNumber str = do
  world <- get
  case Map.lookup str $ numbers world of
    Just number -> return number

getNumberBalance :: Integer -> VerRes Ident
getNumberBalance number = do
  world <- get
  case Map.lookup number $ addresses world of
    Just name -> return name

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

--TODO: wyodrebnic +1 w curr i numStates do nowej funkcji nextState czy cos
--TODO: te 3 funkcje chyba do wywalenia
addTransToNewStateContr :: String -> [Exp] -> [(Ident, Exp)] -> VerRes ()
addTransToNewStateContr transName guards updates =
  addTransToNewState modifyContract transName guards updates

addTransToNewStateP0 :: String -> [Exp] -> [(Ident, Exp)] -> VerRes ()
addTransToNewStateP0 transName guards updates =
  addTransToNewState modifyPlayer0 transName guards updates

addTransToNewStateP1 :: String -> [Exp] -> [(Ident, Exp)] -> VerRes ()
addTransToNewStateP1 transName guards updates =
  addTransToNewState modifyPlayer1 transName guards updates

addTransToNewState :: ModifyModuleType -> String -> [Exp] -> [(Ident, Exp)] -> VerRes ()
addTransToNewState modifyModule transName guards updates = do
  world <- get
  mod <- modifyModule id
  let newState = numStates mod + 1
  addCustomTrans modifyModule transName (currState mod) newState guards updates
  _ <- modifyModule (setCurrState newState)
  _ <- modifyModule (setNumStates newState)
  return ()

--TODO: te 3 funkcje chyba też do wywalenia
addCustomTransContr :: String -> Integer -> Integer -> [Exp] -> [(Ident, Exp)] -> VerRes ()
addCustomTransContr transName fromState toState guards updates = do
  addCustomTrans modifyContract transName fromState toState guards updates

addCustomTransP0 :: String -> Integer -> Integer -> [Exp] -> [(Ident, Exp)] -> VerRes ()
addCustomTransP0 transName fromState toState guards updates = 
  addCustomTrans modifyPlayer0 transName fromState toState guards updates

addCustomTransP1 :: String -> Integer -> Integer -> [Exp] -> [(Ident, Exp)] -> VerRes ()
addCustomTransP1 transName fromState toState guards updates = 
  addCustomTrans modifyPlayer1 transName fromState toState guards updates

addCustomTrans :: ModifyModuleType -> String -> Integer -> Integer -> [Exp] -> [(Ident, Exp)] -> VerRes ()
addCustomTrans modifyModule transName fromState toState guards updates = do
  world <- get
  mod <- modifyModule id
  let newTrans = newCustomTrans (stateVar mod) transName fromState toState guards updates
  _ <- modifyModule (addTransToModule newTrans)
  return ()

addTransToModule :: Trans -> Module -> Module
addTransToModule tr mod = 
  mod {transs = tr:(transs mod)}

newCustomTrans :: String -> String -> Integer -> Integer -> [Exp] -> [(Ident, Exp)] -> Trans
newCustomTrans stateVar transName fromState toState guards updates =
  (
    transName,
    (EEq (EVar (Ident stateVar)) (EInt fromState)):guards,
    (Ident stateVar, EInt toState):updates
  )

---------------------
-- MONEY TRANSFERS --
---------------------

transferToContract :: Ident -> Exp -> VerRes ()
transferToContract from value = do
  transferMoney from (Ident "contract_balance") (EVar (Ident "MAX_CONTRACT_BALANCE")) value

transferFromContract :: Ident -> Exp -> VerRes ()
transferFromContract to value = do
  transferMoney (Ident "contract_balance") to (EVar (Ident "MAX_USER_BALANCE")) value
  

transferMoney :: Ident -> Ident -> Exp -> Exp -> VerRes ()
transferMoney from to maxTo value = do
  addTransToNewStateContr
    ""
    [EGe (EVar from) value, ELe (EAdd (EVar to) value) maxTo]
    [(from, ESub (EVar from) value), (to, EAdd (EVar to) value)]

--------------------------------
-- CODE GENERATION FROM WORLD --
--------------------------------

-- generates PRISM model code from VerWorld
generatePrism :: VerWorld -> String
generatePrism world = 
  "mdp\n\n" ++
  "const int NUM_STATES_CONTR = " ++
  (show $ numStates $ contract world) ++
  ";\n" ++
  "const int NUM_STATES_P0 = " ++
  (show $ numStates $ player0 world) ++
  ";\n" ++
  "const int NUM_STATES_P1 = " ++
  (show $ numStates $ player1 world) ++
  ";\n\n" ++
  "\nmodule blockchain\n" ++
  (prismVars $ bcVars world) ++
  prismTranss (reverse $ transs $ blockchain world) ++
  "endmodule\n" ++
  "\nmodule contract\n" ++
  "cstate : [1..NUM_STATES_CONTR];\n" ++
  (prismVars $ contrGlobVars world) ++
  (prismVars $ contrLocVars world) ++
  prismTranss (reverse $ transs $ contract world) ++
  "endmodule\n" ++
  "\nmodule player0\n" ++
  "state0 : [1..NUM_STATES_P0];\n" ++
  (prismVars $ p0Vars world) ++
  prismTranss (reverse $ transs $ player0 world) ++
  "endmodule\n" ++
  "\nmodule player1\n" ++
  "state1 : [1..NUM_STATES_P1];\n" ++
  (prismVars $ p1Vars world) ++
  prismTranss (reverse $ transs $ player1 world) ++
  "endmodule"

prismVars :: Map.Map Ident Type -> String
prismVars vars = 
  Map.foldlWithKey
    (\code ident typ -> code ++ (prismShowIdent ident)
      ++ " : " ++ (prismShowType typ) ++ ";\n")
    "" 
    vars

-- generates PRISM code for all the transitions
prismTranss :: [Trans] -> String
prismTranss transs =
  foldl 
    (\acc trans -> acc ++ (prismTrans trans) ++ "\n")
    "" 
    transs
  
prismTrans :: Trans -> String
prismTrans (transName, guards, updates) =
  "[" ++ transName ++ "] " ++ (prismGuards guards) ++ "  ->\n" ++ prismUpdates updates ++ ";\n"

prismGuards :: [Exp] -> String
prismGuards [] = ""

prismGuards (h:t) = 
  "(" ++ prismShowExp h ++ ")\n" ++
    foldl 
      (\acc exp -> acc ++ " & (" ++ (prismShowExp exp) ++ ")\n")
      ""
      t

prismUpdates :: [(Ident, Exp)] -> String
prismUpdates [] = ""

prismUpdates (h:t) = 
  "   " ++ (prismUpdate h) ++
    foldl
      (\acc update -> acc ++ "\n & " ++ (prismUpdate update))
      ""
      t

prismUpdate :: (Ident, Exp) -> String
prismUpdate (ident, exp) =
  "(" ++ (prismShowIdent ident) ++ "' = " ++ (prismShowExp exp) ++ ")"


-- PRISM SHOW --

prismShowType :: Type -> String
prismShowType (TUInt x) = "[0.." ++ (show $ x - 1) ++ "]" 

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
  "value"

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
  case Map.lookup ident (contrGlobVars world) of
    Just typ -> return (Just typ)
    Nothing -> 
      case Map.lookup ident (contrLocVars world) of
        Just typ -> return (Just typ)
        Nothing -> 
          case Map.lookup ident (p0Vars world) of
            Just typ -> return (Just typ)
            Nothing ->
              case Map.lookup ident (p1Vars world) of
                Just typ -> return (Just typ)
                Nothing -> return Nothing

minValue :: Ident -> VerRes Integer
minValue ident = do
  typ <- findVarType ident
  case typ of 
    Just (TUInt x) -> return 0

maxValue :: Ident -> VerRes Integer
maxValue ident = do
  typ <- findVarType ident
  case typ of
    Just (TUInt x) -> return (x - 1)
    


-- negate cond --
negateExp :: Exp -> Exp
negateExp (EEq e1 e2) = (ENe e1 e2)
negateExp (ENe e1 e2) = (EEq e1 e2)
negateExp (ELt e1 e2) = (EGe e1 e2)
negateExp (ELe e1 e2) = (EGt e1 e2)
negateExp (EGt e1 e2) = (ELe e1 e2)
negateExp (EGe e1 e2) = (ELt e1 e2)
