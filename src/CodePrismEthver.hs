module CodePrismEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map

import AbsEthver
import WorldPrismEthver
import AuxPrismEthver

--------------------------------
-- CODE GENERATION FROM WORLD --
--------------------------------

-- generates PRISM model code from VerWorld
generatePrism :: VerWorld -> String
generatePrism world = 
  "mdp\n\n" ++
  "const int ADVERSARY;\n\n" ++ 
  generateConstantConstants ++
  (generateNumStates world) ++
  (generateConstantsFromWorld world) ++
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
  "  balance1 : [0..MAX_USER_BALANCE] init 2;\n"

player0Pream :: String
player0Pream =
  "  state0 : [-1..NUM_PLAYER0_STATES] init 0;\n" ++
  "  critical_section0 : bool;\n"

player1Pream :: String
player1Pream =
  "  state1 : [-1..NUM_PLAYER1_STATES] init 0;\n" ++
  "  critical_section1 : bool;\n"

generateConstantConstants :: String
generateConstantConstants = 
  "const int T_NONE = 0;\n" ++
  "const int T_BROADCAST = 1;\n" ++
  "const int T_EXECUTED = 2;\n" ++
  "const int T_INVALIDATED = 3;\n\n"

generateConstantsFromWorld :: VerWorld -> String
generateConstantsFromWorld world = 
  Map.foldlWithKey
    (\code ident value -> code ++ "const int " ++ (prismShowIdent ident)
      ++ " = " ++ (show value) ++ ";\n")
    ""
    (constants world)

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
  
