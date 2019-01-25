module CodePrismEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map

import AbsEthver
import AuxPrismEthver
import AuxEthver
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
  (prismVars (whichSender $ moduleFun world) (vars $ moduleFun world) (varsInitialValues $ moduleFun world)
    (commitmentsIds world)) ++
  (prismGlobalCommitments (globalCommitments $ moduleFun world)) ++
  "\n" ++ 
  prismTranss (whichSender $ moduleFun world) (reverse $ transs $ moduleFun world) ++
  "endmodule\n\n\n"

blockchainPream :: String
blockchainPream = 
  --"  " ++ sContrSender ++ " : [0..1];\n" ++
  -- TODO: skąd wziąć zakres val?
  --"  " ++ sValue ++ " : [0.." ++ sMaxValue ++ "];\n" ++
  --"  " ++ sTimelocksReleased ++ " : bool init false;"
  "  " ++ sTimeElapsed ++ " : [0.." ++ sMaxTime ++ "] init 0;\n"

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

prismVars :: Ident -> Map.Map Ident Type -> Map.Map Ident Exp -> Map.Map Ident Integer -> String
prismVars senderIdent vars initialValues commitmentsMap = 
  Map.foldlWithKey
    (\code ident typ ->
      case typ of
        TSig _ ->
          code
        TCUInt x ->
          code
        {- Old, to delete
        TCUInt x ->
          let
            globalIdent = case Map.lookup ident commitmentsMap of
              Just nr -> Ident $ sGlobalCommitments ++ "_" ++ show nr
              _ -> error $ unident ident ++ " not found in commitmentsIds"
            initSuffix = " init " ++ (show $ maxTypeValueOfType (TCUInt x))
          in
            code ++ "  " ++ (unident globalIdent)
              ++ " : " ++ (prismShowType typ) ++ initSuffix ++ ";\n"-}
        _ -> 
          let 
            initSuffix = 
              case Map.lookup ident initialValues of
                Nothing -> ""
                Just exp -> " init " ++ prismShowExp senderIdent exp
          in
            code ++ "  " ++ (unident ident)
              ++ " : " ++ (prismShowType typ) ++ initSuffix ++ ";\n")
    "" 
    vars

prismGlobalCommitments :: Map.Map Ident Type -> String
prismGlobalCommitments globalCommitments =
  Map.foldlWithKey
    (\code ident typ ->
      case typ of
        TCUInt x ->
          code ++ "  " ++ (unident ident) ++ " : " ++ (prismShowType typ) ++ " init " ++ show (x + 1) ++ ";\n")
    ""
    globalCommitments
  

-----------------
-- prism Trans --
-----------------

-- generates PRISM code for all the transitions
prismTranss :: Ident -> [Trans] -> String
prismTranss senderIdent transs =
  foldl 
    (\acc trans -> acc ++ (prismTrans senderIdent trans) ++ "\n")
    "" 
    transs
  
prismTrans :: Ident -> Trans -> String
prismTrans senderIdent (transName, guards, updates) =
  "  [" ++ transName ++ "]\n    " ++ (prismGuards senderIdent guards) ++ "  ->\n" ++ 
    prismUpdates senderIdent updates ++ ";\n"

prismGuards :: Ident -> [Exp] -> String
prismGuards _ [] = ""

prismGuards senderIdent (h:t) = 
  "(" ++ prismShowExp senderIdent h ++ ")\n" ++
    foldl 
      (\acc exp -> acc ++ "  & (" ++ (prismShowExp senderIdent exp) ++ ")\n")
      ""
      t

prismUpdates :: Ident -> [Branch] -> String
prismUpdates _ [] = ""

prismUpdates _ [([], _)] = "    true"

prismUpdates senderIdent [updates] = 
  "    " ++ prismUpdatesDeterm senderIdent updates

prismUpdates senderIdent (h:t) = 
  let n = length (h:t) in
    foldl
      (\acc updates -> acc ++ " +\n    1/" ++ (show n) ++ ": " ++
        (prismUpdatesDeterm senderIdent updates))
      ("    1/" ++ (show n) ++ ": " ++ (prismUpdatesDeterm senderIdent h))
      t

prismUpdatesDeterm :: Ident -> Branch -> String
prismUpdatesDeterm senderIdent ((h:t), liv) = 
  --(show liv) ++
  (prismUpdate senderIdent h) ++ 
  foldl
    (\acc update -> acc ++ "\n  & " ++ (prismUpdate senderIdent update))
    ""
    t

prismUpdate :: Ident -> (Ident, Exp) -> String
prismUpdate senderIdent (ident, exp) =
  "(" ++ (unident ident) ++ "' = " ++ (prismShowExp senderIdent exp) ++ ")"


-- PRISM SHOW --

prismShowType :: Type -> String
prismShowType (TUInt x) = "[0.." ++ (show $ x - 1) ++ "]" 
prismShowType (TCUInt x) = "[0.." ++ (show $ x + 1) ++ "]"
prismShowType (TSig x) = "[0.." ++ (show x) ++ "]"
--prismShowType TSig = "[0.." ++ (show sMaxSignatures) ++ "]"
prismShowType (TAddr) = "[0..1]" 
prismShowType TBool = "bool"
prismShowType THash = "[0..1]"

-- TODO: porównanie w PRISM jest =, a w Solidity jest ==. Ale chyba będą i tak dwie różne
-- funkcje w CompilerEth i CompilerPrism. Wspólny chcemy mieć tylko typ Exp.
prismShowExp :: Ident -> Exp -> String

prismShowExp senderIdent (EEq e1 e2) = 
  prismShowExp senderIdent e1 ++ " = " ++ prismShowExp senderIdent e2

prismShowExp senderIdent (ENe e1 e2) = 
  prismShowExp senderIdent e1 ++ " != " ++ prismShowExp senderIdent e2

prismShowExp senderIdent (EAnd e1 e2) = 
  "(" ++ prismShowExp senderIdent e1 ++ " & " ++ prismShowExp senderIdent e2 ++ ")"

prismShowExp senderIdent (EOr e1 e2) =
  "(" ++ prismShowExp senderIdent e1 ++ " | " ++ prismShowExp senderIdent e2 ++ ")"
  
prismShowExp senderIdent (EGt e1 e2) = 
  prismShowExp senderIdent e1 ++ " > " ++ prismShowExp senderIdent e2

prismShowExp senderIdent (EGe e1 e2) = 
  prismShowExp senderIdent e1 ++ " >= " ++ prismShowExp senderIdent e2

prismShowExp senderIdent (ELt e1 e2) = 
  prismShowExp senderIdent e1 ++ " < " ++ prismShowExp senderIdent e2

prismShowExp senderIdent (ELe e1 e2) = 
  prismShowExp senderIdent e1 ++ " <= " ++ prismShowExp senderIdent e2

prismShowExp senderIdent (EAdd e1 e2) =
  prismShowExp senderIdent e1 ++ " + " ++ prismShowExp senderIdent e2

prismShowExp senderIdent (ESub e1 e2) =
  prismShowExp senderIdent e1 ++ " - " ++ prismShowExp senderIdent e2

prismShowExp senderIdent (EMul e1 e2) =
  prismShowExp senderIdent e1 ++ " * " ++ prismShowExp senderIdent e2

prismShowExp senderIdent (EDiv e1 e2) =
  "floor(" ++ prismShowExp senderIdent e1 ++ " / " ++ prismShowExp senderIdent e2 ++ ")"

prismShowExp senderIdent (EMod e1 e2) =
  "mod(" ++ prismShowExp senderIdent e1 ++ ", " ++ prismShowExp senderIdent e2 ++ ")"

prismShowExp senderIdent (ENot e1) =
  "!" ++ prismShowExp senderIdent e1

prismShowExp senderIdent (ENeg e1) =
  "-" ++ prismShowExp senderIdent e1

-- TODO: szukać dokładniej, jeśli nazwy lok/glob się przekrywają
prismShowExp _ (EVar ident) =
  unident ident

prismShowExp _ (EArray ident (EInt x)) = 
  unident ident ++ "_" ++ show x

prismShowExp _ (EInt x) = 
  show x

prismShowExp _ (EStr s) =
  s

prismShowExp senderIdent ESender =
  unident senderIdent

prismShowExp _ EValue =
  sValue

prismShowExp _ ETrue = 
  "true"

prismShowExp _ EFalse = 
  "false"

prismShowExp _ exp = 
  error $ "prismShowExp '" ++ show exp ++ "' not implemented" 
