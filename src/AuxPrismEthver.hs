module AuxPrismEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map

import AbsEthver
import ErrM


-- TYPES --

type VerRes a = State VerWorld a

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
  --sender :: [Exp],
  --value :: [Exp],
  currStateContr :: Integer,
  numStatesContr :: Integer,
  currStateP0 :: Integer,
  numStatesP0 :: Integer,
  currStateP1 :: Integer,
  numStatesP1 :: Integer,
  bcTranss :: [Trans],
  contrTranss :: [Trans],
  p0Transs :: [Trans],
  p1Transs :: [Trans]
  }

type Trans = ([Exp], [(Ident, Exp)])


-- INITIALIZATION --

emptyVerWorld :: VerWorld
emptyVerWorld = VerWorld {props = "", contrGlobVars = Map.empty, bcVars = Map.empty,
  contrLocVars = Map.empty, p0Vars = Map.empty, p1Vars = Map.empty,
  funs = Map.empty, addresses = Map.empty, numbers = Map.empty, returnVar = [], 
  currStateContr = 1, numStatesContr = 1, currStateP0 = 1, numStatesP0 = 1, currStateP1 = 1, numStatesP1 = 1,
  bcTranss = [], contrTranss = [], p0Transs = [], p1Transs = []}


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



-- TODO: Na razie mamy jedną uniwersalną zmienną na argument

{-
addArg :: Ident -> Arg -> VerRes ()
addArg (Ident funName) arg = do
  case arg of
    (Ar typ (Ident varName)) -> do
      -- TODO: na pewno ten typ zmiennych?
      addContrGlobVar typ (Ident (funName ++ "_" ++ varName))
-}


-- Może zrobić unikalne nazwy zmiennych będących argumentami funkcji?
-- Chyba wystarczy zrobić stos map, żeby działało zagnieżdżanie wywołań

{-addArgMap :: [Arg] -> [Exp] -> VerRes ()
addArgMap args argsVals = do
  world <- get
  put (world {argMap = Map.fromList $ zip argsNames argsVals})
  where argsNames = map (\(Ar typ ident) -> ident) args

clearArgMap :: VerRes ()
clearArgMap = do
  world <- get
  put (world {argMap = Map.empty})
-}

{-
addSender :: Exp -> VerRes ()
addSender newSender = do
  world <- get
  put (world {sender = newSender:(sender world)})

getSender :: VerRes Exp
getSender = do
  world <- get
  return $ head $ sender world

removeSender :: VerRes ()
removeSender = do
  world <- get
  put (world {sender = tail $ sender world})
-}

{-
addValue :: Exp -> VerRes ()
addValue newValue = do
  world <- get
  put (world {value = newValue:(value world)})

getValue :: VerRes Exp
getValue = do
  world <- get
  return $ head $ value world

removeValue :: VerRes ()
removeValue = do
  world <- get
  put (world {value = tail $ value world})
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


-----------
-- Trans --
-----------

--TODO: wyodrebnic +1 w curr i numStates do nowej funkcji nextState czy cos
addTransContr :: [Exp] -> [(Ident, Exp)] -> VerRes ()
addTransContr guards updates = do
  world <- get
  addCustomTransContr (currStateContr world) (numStatesContr world + 1) guards updates
  world <- get
  put (world {
    currStateContr = (numStatesContr world) + 1, 
    numStatesContr = (numStatesContr world) + 1
    })

addTransP0 :: [Exp] -> [(Ident, Exp)] -> VerRes ()
addTransP0 guards updates = do
  world <- get
  addCustomTransP0 (currStateP0 world) (numStatesP0 world + 1) guards updates
  world <- get
  put (world {
    currStateP0 = (numStatesP0 world) + 1, 
    numStatesP0 = (numStatesP0 world) + 1
    })

addTransP1 :: [Exp] -> [(Ident, Exp)] -> VerRes ()
addTransP1 guards updates = do
  world <- get
  addCustomTransP1 (currStateP1 world) (numStatesP1 world + 1) guards updates
  world <- get
  put (world {
    currStateP1 = (numStatesP1 world) + 1, 
    numStatesP1 = (numStatesP1 world) + 1
    })

addCustomTransContr :: Integer -> Integer -> [Exp] -> [(Ident, Exp)] -> VerRes ()
addCustomTransContr fromState toState guards updates = do
  world <- get
  let newContrTranss = newCustomTrans "cstate" fromState toState guards updates
  put (world {contrTranss = newContrTranss:(contrTranss world)})

addCustomTransP0 :: Integer -> Integer -> [Exp] -> [(Ident, Exp)] -> VerRes ()
addCustomTransP0 fromState toState guards updates = do
  world <- get
  let newP0Transs = newCustomTrans "state0" fromState toState guards updates
  put (world {p0Transs = newP0Transs:(p0Transs world)})

addCustomTransP1 :: Integer -> Integer -> [Exp] -> [(Ident, Exp)] -> VerRes ()
addCustomTransP1 fromState toState guards updates = do
  world <- get
  let newP1Transs = newCustomTrans "state1" fromState toState guards updates
  put (world {p1Transs = newP1Transs:(p1Transs world)})


newCustomTrans :: String -> Integer -> Integer -> [Exp] -> [(Ident, Exp)] -> Trans
newCustomTrans stateVar fromState toState guards updates =
  (
    ((EEq (EVar (Ident stateVar)) (EInt fromState)):guards,
    (Ident stateVar, EInt toState):updates)
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
  addTransContr
    [EGe (EVar from) value, ELe (EAdd (EVar to) value) maxTo]
    [(from, ESub (EVar from) value), (to, EAdd (EVar to) value)]


-- CODE GENERATION FROM WORLD --

-- generates PRISM model code from VerWorld
generatePrism :: VerWorld -> String
generatePrism world = 
  "mdp\n\n" ++
  "const int NUM_STATES_CONTR = " ++
  (show $ numStatesContr world) ++
  ";\n" ++
  "const int NUM_STATES_P0 = " ++
  (show $ numStatesP0 world) ++
  ";\n" ++
  "const int NUM_STATES_P1 = " ++
  (show $ numStatesP1 world) ++
  ";\n\n" ++
  "\nmodule blockchain\n" ++
  (prismVars $ bcVars world) ++
  prismTranss (reverse $ bcTranss world) ++
  "endmodule\n" ++
  "\nmodule contract\n" ++
  "cstate : [1..NUM_STATES_CONTR];\n" ++
  (prismVars $ contrGlobVars world) ++
  (prismVars $ contrLocVars world) ++
  prismTranss (reverse $ contrTranss world) ++
  "endmodule\n" ++
  "\nmodule player0\n" ++
  "state0 : [1..NUM_STATES_P0];\n" ++
  (prismVars $ p0Vars world) ++
  prismTranss (reverse $ p0Transs world) ++
  "endmodule\n" ++
  "\nmodule player1\n" ++
  "state1 : [1..NUM_STATES_P1];\n" ++
  (prismVars $ p1Vars world) ++
  prismTranss (reverse $ p1Transs world) ++
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
prismTrans (guards, updates) =
  prismGuards guards ++ "  ->\n" ++ prismUpdates updates ++ ";\n"

prismGuards :: [Exp] -> String
prismGuards [] = ""

prismGuards (h:t) = 
  "[] (" ++ prismShowExp h ++ ")\n" ++
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
