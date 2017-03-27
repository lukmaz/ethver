module CodePrismEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map

import AbsEthver
import AuxPrismEthver
import ConstantsEthver
import WorldPrismEthver

--------------------------------
-- CODE GENERATION FROM WORLD --
--------------------------------

-- generates PRISM model code from VerWorld
generatePrism :: VerWorld -> String
generatePrism world = 
  "mdp\n\n" ++
  "const int " ++ sAdversaryFlag ++ ";\n\n" ++ 
  generateConstantConstants ++
  (generateNumStates world) ++
  (generateConstantsFromWorld world) ++
  (generateModule blockchain sBCModule blockchainPream world) ++
  (generateModule contract sContrModule contractPream world) ++
  (generateModule communication sCommModule communicationPream world) ++
  (generateModule player0 sP0Module player0Pream world) ++
  (generateModule player1 sP1Module player1Pream world)

generateModule :: (VerWorld -> Module) -> String -> String ->VerWorld -> String
generateModule moduleFun moduleName pream world = 
  "\n\n/////////////////////\n" ++
  "\nmodule " ++ moduleName ++ "\n" ++
  pream ++ "\n" ++
  (prismVars (vars $ moduleFun world) (varsInitialValues $ moduleFun world)) ++
  "\n" ++ 
  prismTranss (reverse $ transs $ moduleFun world) ++
  "endmodule\n\n\n"

blockchainPream :: String
blockchainPream = "";
  --"  " ++ sContrSender ++ " : [0..1];\n" ++
  -- TODO: skąd wziąć zakres val?
  --"  " ++ sValue ++ " : [0.." ++ sMaxValue ++ "];\n" ++
  --"  " ++ sTimelocksReleased ++ " : bool init false;"

contractPream :: String
contractPream =
  "  " ++ sContrState ++ " : [0.." ++ sNumContractStates ++ "] init " ++ (show nInitContractState) ++ ";\n" ++
  "  " ++ sNextState ++ " : [0.." ++ sNumContractStates ++ "];\n" ++
  --  "  " ++ sContractBalance ++ " : [0.." ++ sMaxContractBalance ++ "] init " ++ sInitContractBalance ++ ";\n" ++
  "  " ++ sP0Balance ++ " : [0.." ++ sMaxUserBalance ++ "] init " ++ sInitUser0Balance ++ ";\n" ++
  "  " ++ sP1Balance ++ " : [0.." ++ sMaxUserBalance ++ "] init " ++ sInitUser1Balance ++ ";\n"

communicationPream :: String
communicationPream = 
  -- "  " ++ sCommSender ++ " : [0..1];\n" ++
  -- TODO: state 0 not used
  "  " ++ sCommState ++ " : [0.." ++ sNumCommStates ++ "] init " ++ (show nInitCommState) ++ ";\n" 

player0Pream :: String
player0Pream =
  "  " ++ sP0State ++ " : [" ++ (show nMinP0State) ++ ".." ++ sNumP0States ++ "] init " ++ 
  (show nInitP0State) ++ ";\n" 
  -- critical section
  -- ++ "  " ++ sCriticalSection0 ++ " : bool;\n"

player1Pream :: String
player1Pream =
  "  " ++ sP1State ++ " : [" ++ (show nMinP1State) ++ ".." ++ sNumP1States ++ "] init " ++ (show nInitP1State) ++
  ";\n" 
  -- critical section
  -- ++ "  " ++ sCriticalSection1 ++ " : bool;\n"

generateConstantConstants :: String
generateConstantConstants = 
  "const int " ++ sTNone ++ " = " ++ (show nTNone) ++ ";\n" ++
  "const int " ++ sTBroadcast ++ " = " ++ (show nTBroadcast) ++ ";\n" ++
  "const int " ++ sTExecuted ++ " = " ++ (show nTExecuted) ++ ";\n" ++
  "const int " ++ sTInvalidated ++ " = " ++ (show nTInvalidated) ++ ";\n\n"

generateConstantsFromWorld :: VerWorld -> String
generateConstantsFromWorld world = 
  Map.foldlWithKey
    (\code ident value -> code ++ "const int " ++ (unident ident)
      ++ " = " ++ (show value) ++ ";\n")
    ""
    (constants world)

generateNumStates :: VerWorld -> String
generateNumStates world = 
  "const int " ++ sNumContractStates ++ " = " ++
  (show $ numStates $ contract world) ++
  ";\n" ++
  "const int " ++ sNumCommStates ++ " = " ++
  (show $ numStates $ communication world) ++
  ";\n" ++
  "const int " ++ sNumP0States ++ " = " ++
  (show $ numStates $ player0 world) ++
  ";\n" ++
  "const int " ++ sNumP1States ++ " = " ++
  (show $ numStates $ player1 world) ++
  ";\n\n"

prismVars :: Map.Map Ident Type -> Map.Map Ident Exp -> String
prismVars vars initialValues = 
  Map.foldlWithKey
    (\code ident typ -> 
      let 
        initSufix = 
          case Map.lookup ident initialValues of
            Nothing -> ""
            Just exp -> " init " ++ prismShowExp exp
      in
        code ++ "  " ++ (unident ident)
          ++ " : " ++ (prismShowType typ) ++ initSufix ++ ";\n")
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

prismUpdates [[]] = "    true"

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
  "(" ++ (unident ident) ++ "' = " ++ (prismShowExp exp) ++ ")"


-- PRISM SHOW --

prismShowType :: Type -> String
prismShowType (TUInt x) = "[0.." ++ (show $ x - 1) ++ "]" 
prismShowType (TRUInt x) = "[0.." ++ (show x) ++ "]"
prismShowType TBool = "bool"

-- TODO: porównanie w ver jest =, a w sol jest ==. Ale chyba będą i tak dwie różne
-- funkcje w CompilerEth i CompilerPrism. Wspólny chcemy mieć tylko typ Exp.
prismShowExp :: Exp -> String

prismShowExp (EEq e1 e2) = 
  prismShowExp e1 ++ " = " ++ prismShowExp e2

prismShowExp (ENe e1 e2) = 
  prismShowExp e1 ++ " != " ++ prismShowExp e2

prismShowExp (EAnd e1 e2) = 
  "(" ++ prismShowExp e1 ++ " & " ++ prismShowExp e2 ++ ")"

prismShowExp (EOr e1 e2) =
  "(" ++ prismShowExp e1 ++ " | " ++ prismShowExp e2 ++ ")"
  
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
  unident ident

prismShowExp (EInt x) = 
  show x

prismShowExp (EStr s) =
  s

--prismShowExp ESender =
--  sSender

prismShowExp EValue =
  sValue

prismShowExp ETrue = 
  "true"

prismShowExp EFalse = 
  "false"

-- TODO SExp, do skopiowania do sendT, sendC, wait, rand, rand_lazy itp. (?)
{-
prismShowExp (ECall (h:t) args) =
  foldl
    (\acc ident -> acc ++ "." ++ (unident ident))
    (unident h)
    t
-}

-- TODO: czy to jest w ogóle używane? Robi coś dziwnego
prismShowExp (ECall ident args) =
  unident ident

