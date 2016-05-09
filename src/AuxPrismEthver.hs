module AuxPrismEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map

import AbsEthver
import ErrM


-- TYPES --

type VerRes a = State VerWorld a

data VerWorld = VerWorld {
  props :: String,
  coVars :: Map.Map Ident Type,
  scVars :: Map.Map Ident Type,
  loVars :: Map.Map Ident Type,
  funs :: Map.Map Ident Function,
  argMap :: Map.Map Ident Exp,
  addresses :: Map.Map Integer Ident,
  numbers :: Map.Map String Integer,
  returnVar :: [Ident],
  sender :: [Exp],
  value :: [Exp],
  currState :: Integer,
  numStates :: Integer,
  transs :: [Trans] }

type Trans = ([Exp], [(Ident, Exp)])


-- INITIALIZATION --

emptyVerWorld :: VerWorld
emptyVerWorld = VerWorld {props = "", coVars = Map.empty, scVars = Map.empty, loVars = Map.empty,
  funs = Map.empty, argMap = Map.empty, addresses = Map.empty, numbers = Map.empty, returnVar = [], sender = [], value = [], 
  currState = 1, numStates = 1, transs = []}


-- WORLD MODIFICATION --

addProps :: String -> VerRes ()
addProps text = do
  world <- get
  put (world {props = (props world) ++ text})

addCoVar :: Type -> Ident -> VerRes ()
addCoVar typ ident = do
  world <- get
  put (world {coVars = Map.insert ident typ (coVars world)})

addScVar :: Type -> Ident -> VerRes ()
addScVar typ ident = do
  world <- get
  put (world {scVars = Map.insert ident typ (scVars world)})

addLoVar :: Type -> Ident -> VerRes ()
addLoVar typ ident = do
  world <- get
  put (world {loVars = Map.insert ident typ (loVars world)})

-- TODO: ograniczyć deklaracje zmiennych tylko na początek funkcji
-- i tutaj dodać wszystkie deklaracje do loVars
addFun :: Function -> VerRes ()
addFun (Fun name args stms) = do
  world <- get
  put (world {funs = Map.insert name (Fun name args stms) (funs world)})

addFun (FunR name args retTyp stms) = do
  addLoVar retTyp (Ident (prismShowIdent name ++ "_retVal"))
  world <- get
  put (world {funs = Map.insert name (FunR name args retTyp stms) (funs world)})

-- Może zrobić unikalne nazwy zmiennych będących argumentami funkcji?
-- Chyba wystarczy zrobić stos map, żeby działało zagnieżdżanie wywołań
addArgMap :: [Arg] -> [Exp] -> VerRes ()
addArgMap args argsVals = do
  world <- get
  put (world {argMap = Map.fromList $ zip argsNames argsVals})
  where argsNames = map (\(Ar typ ident) -> ident) args

clearArgMap :: VerRes ()
clearArgMap = do
  world <- get
  put (world {argMap = Map.empty})

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

--TODO: wyodrebnic +1 w curr i numStates do nowej funkcji nextState czy cos
addTrans :: [Exp] -> [(Ident, Exp)] -> VerRes ()
addTrans guards updates = do
  world <- get
  addCustomTrans (currState world) (numStates world + 1) guards updates
  world <- get
  put (world {
    currState = (numStates world) + 1, 
    numStates = (numStates world) + 1
    })

addCustomTrans :: Integer -> Integer -> [Exp] -> [(Ident, Exp)] -> VerRes ()
addCustomTrans fromState toState guards updates = do
  world <- get
  put (world {
    transs = 
      (
        ((EEq (EVar (Ident "state")) (EInt fromState)):guards,
        (Ident "state", EInt toState):updates)
      )
      :
      (transs world)
    })


-- MONEY TRANSFERS --

transferToContract :: Ident -> Exp -> VerRes ()
transferToContract from value = do
  transferMoney from (Ident "contract_balance") (EVar (Ident "MAX_CONTRACT_BALANCE")) value

transferFromContract :: Ident -> Exp -> VerRes ()
transferFromContract to value = do
  transferMoney (Ident "contract_balance") to (EVar (Ident "MAX_USER_BALANCE")) value
  

transferMoney :: Ident -> Ident -> Exp -> Exp -> VerRes ()
transferMoney from to maxTo value = do
  addTrans
    [EGe (EVar from) value, ELe (EAdd (EVar to) value) maxTo]
    [(from, ESub (EVar from) value), (to, EAdd (EVar to) value)]


-- CODE GENERATION FROM WORLD --

-- generates PRISM model code from VerWorld
generatePrism :: VerWorld -> String
generatePrism world = 
  "mdp\n\n" ++
  "const int NUM_STATES = " ++
  (show $ numStates world) ++
  ";\n\n" ++
  prismGlobals world ++
  "\nmodule player\n" ++
  prismTranss (reverse $ transs world) ++
  "endmodule"

-- generates PRISM code for global variables
-- TODO: dodawanie przedrostków nazw zmiennych co_, sc_, lo_
prismGlobals :: VerWorld -> String
prismGlobals world = 
  Map.foldlWithKey
    (\code ident typ -> code ++ "global " ++ (prismShowIdent ident)
      ++ " : " ++ (prismShowType typ) ++ ";\n")
    "" 
    (coVars world)
  ++ 
  Map.foldlWithKey
    (\code ident typ -> code ++ "global " ++ (prismShowIdent ident)
      ++ " : " ++ (prismShowType typ) ++ ";\n")
    "" 
    (scVars world)
  ++ 
  Map.foldlWithKey
    (\code ident typ -> code ++ "global " ++ (prismShowIdent ident)
      ++ " : " ++ (prismShowType typ) ++ ";\n")
    "" 
    (loVars world)
  ++
  "global state : [1..NUM_STATES];\n"

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
  case Map.lookup ident (loVars world) of
    Just typ -> return (Just typ)
    Nothing -> 
      case Map.lookup ident (coVars world) of
        Just typ -> return (Just typ)
        Nothing ->
          case Map.lookup ident (scVars world) of
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
