module CompilerPrismEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map

import AbsEthver
import AuxPrismEthver


-- TODO: zliczanie stanów

-- generates (prism model code, prism properties)
verTree :: Program -> (String, String)
verTree prog =
  let (a, world) = (runState (verProgram prog)) emptyVerWorld
  in (generatePrism world, props world)

verProgram :: Program -> VerRes ()
verProgram (Prog contract scenario) = do
  verContract contract
  verScenario scenario

--------------
-- CONTRACT --
--------------

verContract :: Contract -> VerRes ()
verContract (Contr name users decls funs) = do
  mapM_ addUser users
  mapM_ verCoDecl decls
  mapM_ verCoFun funs

-- TODO: globalne, nieglobalne
verCoDecl :: Decl -> VerRes ()
verCoDecl (Dec typ ident) = do
  addContrVar typ ident

verCoFun :: Function -> VerRes ()
verCoFun (Fun name args stms) = do
  --addFun fun
  world <- get
  -- TODO argumenty
  mapM_ addArg args
  -- TODO: czy tu musi być verCoStm?
  mapM_ (verStm modifyContract) stms


addUser :: UserDecl -> VerRes ()
addUser (UDec name) = do
  addAddress name

--------------
-- SCENARIO --
--------------

verScenario :: Scenario -> VerRes ()
verScenario (Scen decls stms) = do
  mapM_ verScDecl decls
  -- TODO: P0
  mapM_ (verStm modifyPlayer0) stms

-- TODO: Drugi gracz
verScDecl :: Decl -> VerRes ()
verScDecl (Dec typ ident) = do
  addP0Var typ ident

-----------
-- CoStm --
-----------

verStm :: ModifyModuleType -> Stm -> VerRes ()
verStm modifyModule (SExp exp) = do
  _ <- verExp modifyModule exp
  return ()
  
verStm modifyModule (SReturn exp) = do
  evalExp <- verExp modifyModule exp
  world <- get
  _ <- verExp modifyModule (EAss (head $ returnVar world) evalExp)
  return ()

-- TODO: drugi gracz
-- TODO: zrobić, żeby return wychodziło z wykonania bieżącej funkcji
verStm modifyModule (SIf cond ifBlock) = do
  evalCond <- verExp modifyModule cond
  world <- get
  mod <- modifyModule id
  let ifState = currState mod
  addTransToNewState
    modifyModule
    ""
    [evalCond]
    []
  verStm modifyModule ifBlock
  world <- get
  mod <- modifyModule id
  addCustomTrans
    modifyModule
    ""
    ifState
    (currState mod)
    [negateExp evalCond]
    []

-- TODO: drugi gracz, kontrakt
verStm modifyModule (SIfElse cond ifBlock elseBlock) = do
  evalCond <- verExp modifyModule cond
  world <- get
  mod <- modifyModule id
  let ifState = currState mod
  addTransToNewState
    modifyModule
    ""
    [evalCond]
    []
  verStm modifyModule ifBlock
  world <- get
  mod <- modifyModule id
  let endIfState = currState mod 
  addCustomTrans
    modifyModule
    ""
    ifState
    (numStates mod + 1)
    [negateExp evalCond]
    []
  world <- get
  mod <- modifyModule id
  let newState = numStates mod + 1
  modifyModule (setCurrState newState)
  modifyModule (setNumStates newState)
  verStm modifyModule elseBlock
  world <- get
  mod <- modifyModule id
  addCustomTrans
    modifyModule
    ""
    (currState mod)
    endIfState
    []
    []
  _ <- modifyModule (setCurrState endIfState)
  return ()
  
verStm modifyModule (SBlock stms) = do
  mapM_ (verStm modifyModule) stms


-----------
-- Exp --
-----------

verExp :: ModifyModuleType -> Exp -> VerRes Exp

verExp modifyModule (EEq exp1 exp2) = verMathExp modifyModule (EEq exp1 exp2)
verExp modifyModule (EAdd exp1 exp2) = verMathExp modifyModule (EAdd exp1 exp2)
verExp modifyModule (ESub exp1 exp2) = verMathExp modifyModule (ESub exp1 exp2)
verExp modifyModule (EMul exp1 exp2) = verMathExp modifyModule (EMul exp1 exp2)
verExp modifyModule (EDiv exp1 exp2) = verMathExp modifyModule (EDiv exp1 exp2)
verExp modifyModule (EMod exp1 exp2) = verMathExp modifyModule (EMod exp1 exp2)

verExp modifyModule (EAss ident exp) = verValExp modifyModule (EAss ident exp)
verExp modifyModule (EVar ident) = verValExp modifyModule (EVar ident)
verExp modifyModule EValue = verValExp modifyModule EValue
verExp modifyModule ESender = verValExp modifyModule ESender
verExp modifyModule (EInt x) = verValExp modifyModule (EInt x)
verExp modifyModule (EStr s) = verValExp modifyModule (EStr s)

verExp modifyModule (ECall idents exps) = verCallExp modifyModule (ECall idents exps)
verExp modifyModule (ESend receiver args) = verCallExp modifyModule (ESend receiver args)


-------------
-- MathExp --
-------------

verMathExp :: ModifyModuleType -> Exp -> VerRes Exp

verMathExp modifyModule (EEq exp1 exp2) = do
  evalExp1 <- verExp modifyModule exp1
  evalExp2 <- verExp modifyModule exp2
  return (EEq evalExp1 evalExp2)

verMathExp modifyModule (EAdd exp1 exp2) = do
  evalExp1 <- verExp modifyModule exp1
  evalExp2 <- verExp modifyModule exp2
  return (EAdd evalExp1 evalExp2)

verMathExp modifyModule (ESub exp1 exp2) = do
  evalExp1 <- verExp modifyModule exp1
  evalExp2 <- verExp modifyModule exp2
  return (ESub evalExp1 evalExp2)

verMathExp modifyModule (EMul exp1 exp2) = do
  evalExp1 <- verExp modifyModule exp1
  evalExp2 <- verExp modifyModule exp2
  return (EMul evalExp1 evalExp2)

verMathExp modifyModule (EDiv exp1 exp2) = do
  evalExp1 <- verExp modifyModule exp1
  evalExp2 <- verExp modifyModule exp2
  return (EDiv evalExp1 evalExp2)

verMathExp modifyModule (EMod exp1 exp2) = do
  evalExp1 <- verExp modifyModule exp1
  evalExp2 <- verExp modifyModule exp2
  return (EMod evalExp1 evalExp2)


------------
-- ValExp --
------------

-- TODO: automatyczna generacja standardowego przejścia na nast. stan
-- TODO: na razie tylko P0
verValExp :: ModifyModuleType -> Exp -> VerRes Exp

verValExp modifyModule (EAss ident exp) = do
  evalExp <- verExp modifyModule exp
  world <- get
  minV <- minValue ident
  maxV <- maxValue ident
  addTransToNewState
    modifyModule
    ""
    [EGe evalExp (EInt minV), ELe evalExp (EInt maxV)]
    [(ident, evalExp)]
  return (EAss ident evalExp)

verValExp modifyModule (EVar ident) = do
  world <- get
  case Map.lookup ident (vars $ blockchain world) of
    Just exp ->
      return (EVar ident)
    Nothing ->
      case Map.lookup ident (vars $ contract world) of
        Just exp ->
          return (EVar ident)
        Nothing ->
          case Map.lookup ident (vars $ player0 world) of
            Just exp ->
              return (EVar ident)
            Nothing ->
              case Map.lookup ident (vars $ player1 world) of
                Just exp ->
                  return (EVar ident)

verValExp modifyModule EValue = do
  return EValue

verValExp modifyModule ESender = do
  return ESender

verValExp modifyModule (EInt x) =
  return (EInt x)

verValExp modifyModule (EStr s) = do
  number <- getAddressNumber s
  addProps ("getAddress Number " ++ s ++ " = " ++ (show number) ++ "\n")
  return (EInt number)


----------------
-- CallExp --
----------------

-- TODO: na razie możemy mieć tylko jeden kontrakt
verCallExp :: ModifyModuleType -> Exp -> VerRes Exp

verCallExp modifyModule (ECall idents exps) = do
  case idents of
    [funName, (Ident "sendTransaction")] -> do 
      verSendTAux modifyModule funName exps
      return (ECall idents exps)
    [funName, (Ident "call")] -> do
      verCallAux modifyModule funName exps

verCallExp modifyModule (ESend receiverExp args) = do
  case args of
    [AExp val] -> do
      receiverEval <- verExp modifyModule receiverExp
      case receiverEval of
        EStr receiverAddress -> do
          receiverNumber <- getAddressNumber receiverAddress
          receiverBalance <- getNumberBalance receiverNumber
          transferFromContract receiverBalance val
        EInt receiverNumber -> do
          receiverBalance <- getNumberBalance receiverNumber
          transferFromContract receiverBalance val
  return (ESend receiverExp args)

-----------------------------
-- Call auxilary functions --
-----------------------------

-- TODO: chyba powinno być najpierw kopiowanie coVars i scVars (?) na lokalne
verCallAux :: ModifyModuleType -> Ident -> [CallArg] -> VerRes Exp
verCallAux modifyModule funName argsVals = do
  world <- get
  case Map.lookup funName (funs world) of
    Just fun -> verFunCall modifyModule fun argsVals

verFunCall :: ModifyModuleType -> Function -> [CallArg] -> VerRes Exp
verFunCall modifyModule (FunR name args ret stms) argsVals = do
  let expArgsVals = map (\(AExp exp) -> exp) argsVals
  mapM_ (addArgMap modifyModule) $ zip args expArgsVals
  let retVarIdent = Ident ((prismShowIdent name) ++ "_retVal")
  addReturnVar retVarIdent
  mapM_ (verStm modifyModule) stms
  removeReturnVar
  return (EVar retVarIdent)
--TODO: to jest przepisane z verScFunSendT


-- ScSendT --

verSendTAux :: ModifyModuleType -> Ident -> [CallArg] -> VerRes ()
verSendTAux modifyModule funName argsVals = do
  -- TODO: chyba dopiero potrzebne przy argumentach
  --case Map.lookup funName (funs world) of
  --  Just fun -> verFunSendT modifyModule fun argsVals

  --TODO: P0
  let expArgsVals = map (\(AExp exp) -> exp) (init argsVals)
  let (ABra _ value) = last argsVals
  addTransToNewState 
    modifyModule 
    ("broadcast_" ++ (prismShowIdent funName) ++ "0") 
    [EEq (EVar (Ident "cstate")) (EInt 1)]
    [(Ident $ (prismShowIdent funName) ++ "_val" ++ "0", value)]

  addTransToNewState
    modifyModule
    ""
    -- TODO: 0
    [EEq (EVar (Ident "cstate")) (EInt 1), EEq (EVar (Ident (prismShowIdent funName ++ "_state" ++ "0"))) (EVar (Ident "T_EXECUTED"))]
    []


-- TODO: nie działają zagnieżdżone funkcje. 
-- Chyba musi być wielopoziomowy argMap
-- To jest wersja dla sendTransaction, dla call powinno być co innego
{-

verFunSendT :: ModifyModuleType -> Function -> [CallArg] -> VerRes ()
verFunSendT modifyModule (Fun name args stms) argsVals = do
  let expArgsVals = map (\(AExp exp) -> exp) (init argsVals)
  let (ABra sender value) = last argsVals
  mapM_ (addArgMap modifyModule) $ zip args expArgsVals
  --addSender sender
  --addValue value
  case sender of
    EStr str -> do
      addAddress str
      when 
        (value /= (EInt 0)) 
        (do
          number <- getAddressNumber str
          balance <- getNumberBalance number
          transferToContract balance value)
      mapM_ (verStm modifyModule) stms
  --removeValue
  --removeSender

verFunSendT modifyModule (FunR name args ret stms) argsVals =
  verFunSendT modifyModule (Fun name args stms) argsVals
-}

addArg :: Arg -> VerRes ()
addArg (Ar typ ident) = do
  -- TODO: sztywna nazwa "arg"
  addBcVar typ ident

addArgMap :: ModifyModuleType -> (Arg, Exp) -> VerRes ()
addArgMap modifyModule ((Ar typ ident), exp) = do
  verExp modifyModule (EAss ident exp)
  return ()
