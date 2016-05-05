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
verContract (Contr name decls funs) = do
  mapM_ verCoDecl decls
  mapM_ verCoFun funs

-- TODO: globalne, nieglobalne
verCoDecl :: Decl -> VerRes ()
verCoDecl (Dec typ ident) = do
  addCoVar typ ident

verCoFun :: Function -> VerRes ()
verCoFun fun =
  addFun fun


--------------
-- SCENARIO --
--------------

verScenario :: Scenario -> VerRes ()
verScenario (Scen decls stms) = do
  mapM_ verScDecl decls
  mapM_ verScStm stms

-- TODO: local variables
verScDecl :: Decl -> VerRes ()
verScDecl (Dec typ ident) = do
  addScVar typ ident

-----------
-- ScStm --
-----------

verScStm :: Stm -> VerRes ()
verScStm (SExp exp) = do
  _ <- verScExp exp
  return ()
  
verScStm (SReturn exp) = do
  evalExp <- verScExp exp
  world <- get
  _ <- verScExp (EAss (head $ returnVar world) evalExp)
  return ()

-- TODO: zrobić, żeby return wychodziło z wykonania bieżącej funkcji
verScStm (SIf cond ifBlock) = do
  evalCond <- verScExp cond
  world <- get
  let ifState = currState world
  addTrans
    [evalCond]
    []
  verScStm ifBlock
  world <- get
  addCustomTrans
    ifState
    (currState world)
    [negateExp evalCond]
    []

verScStm (SIfElse cond ifBlock elseBlock) = do
  evalCond <- verScExp cond
  world <- get
  let ifState = currState world
  addTrans
    [evalCond]
    []
  verScStm ifBlock
  world <- get
  let endIfState = currState world
  addCustomTrans
    ifState
    (numStates world + 1)
    [negateExp evalCond]
    []
  world <- get
  put (world {currState = numStates world + 1, numStates = numStates world + 1})
  verScStm elseBlock
  world <- get
  addCustomTrans
    (currState world)
    endIfState
    []
    []
  world <- get
  put (world {currState = endIfState})
  
      

-----------
-- ScExp --
-----------

verScExp :: Exp -> VerRes Exp

verScExp (EEq exp1 exp2) = verMathExp (EEq exp1 exp2)
verScExp (EAdd exp1 exp2) = verMathExp (EAdd exp1 exp2)
verScExp (ESub exp1 exp2) = verMathExp (ESub exp1 exp2)
verScExp (EMul exp1 exp2) = verMathExp (EMul exp1 exp2)
verScExp (EDiv exp1 exp2) = verMathExp (EDiv exp1 exp2)
verScExp (EMod exp1 exp2) = verMathExp (EMod exp1 exp2)

verScExp (EAss ident exp) = verValExp (EAss ident exp)
verScExp (EVar ident) = verValExp (EVar ident)
verScExp EValue = verValExp EValue
verScExp ESender = verValExp ESender
verScExp (EInt x) = verValExp (EInt x)
verScExp (EStr s) = verValExp (EStr s)

verScExp (ECall idents exps) = verCallExp (ECall idents exps)
verScExp (ESend receiver args) = verCallExp (ESend receiver args)


-------------
-- MathExp --
-------------

verMathExp (EEq exp1 exp2) = do
  evalExp1 <- verScExp exp1
  evalExp2 <- verScExp exp2
  return (EEq evalExp1 evalExp2)

verMathExp (EAdd exp1 exp2) = do
  evalExp1 <- verScExp exp1
  evalExp2 <- verScExp exp2
  return (EAdd evalExp1 evalExp2)

verMathExp (ESub exp1 exp2) = do
  evalExp1 <- verScExp exp1
  evalExp2 <- verScExp exp2
  return (ESub evalExp1 evalExp2)

verMathExp (EMul exp1 exp2) = do
  evalExp1 <- verScExp exp1
  evalExp2 <- verScExp exp2
  return (EMul evalExp1 evalExp2)

verMathExp (EDiv exp1 exp2) = do
  evalExp1 <- verScExp exp1
  evalExp2 <- verScExp exp2
  return (EDiv evalExp1 evalExp2)

verMathExp (EMod exp1 exp2) = do
  evalExp1 <- verScExp exp1
  evalExp2 <- verScExp exp2
  return (EMod evalExp1 evalExp2)


------------
-- ValExp --
------------

-- TODO: automatyczna generacja standardowego przejścia na nast. stan
verValExp (EAss ident exp) = do
  evalExp <- verScExp exp
  world <- get
  minV <- minValue ident
  maxV <- maxValue ident
  addTrans 
    [EGe evalExp (EInt minV), ELe evalExp (EInt maxV)]
    [(ident, evalExp)]
  return (EAss ident evalExp)

verValExp (EVar ident) = do
  world <- get
  case Map.lookup ident (argMap world) of
    Just exp ->
      verScExp exp
    Nothing -> return (EVar ident)
    -- TODO: przedrostki nazw zmiennych lo_, co_, sc_
    {-
      case Map.lookup ident (loVars world) of
        Just _ -> return (EVar (Ident ("lo_" ++ (prismShowIdent ident))))
        Nothing -> 
          case Map.lookup ident (coVars world) of
            Just _ -> return (EVar (Ident ("co_" ++ (prismShowIdent ident))))
            Nothing ->
              case Map.lookup ident (scVars world) of
                Just _ -> return (EVar (Ident ("sc_" ++ (prismShowIdent ident))))
                Nothing -> do
                  addProps ("Var not found " ++ (prismShowIdent ident) ++ "\n")
                  return (EVar ident)
    -}

verValExp EValue = do
  value <- getValue
  verScExp value

verValExp ESender = do
  sender <- getSender
  verScExp sender

verValExp (EInt x) =
  return (EInt x)

verValExp (EStr s) =
  return (EStr s)


----------------
-- VerCallExp --
----------------

-- TODO: na razie możemy mieć tylko jeden kontrakt
verCallExp (ECall idents exps) = do
  case idents of
    [funName, (Ident "sendTransaction")] -> do 
      verScSendT funName exps
      return (ECall idents exps)
    [funName, (Ident "call")] -> do
      verScCall funName exps

verCallExp (ESend receiverExp args) = do
  case args of
    [AExp val] -> do
      receiverEval <- verScExp receiverExp
      case receiverEval of
        EStr receiverAddress -> do
          receiverBalance <- getAddressBalance receiverAddress
          transferFromContract receiverBalance val
  return (ESend receiverExp args)


-- Call --

-- TODO: chyba powinno być najpierw kopiowanie coVars i scVars (?) na lokalne
verScCall :: Ident -> [CallArg] -> VerRes Exp
verScCall funName argsVals = do
  world <- get
  case Map.lookup funName (funs world) of
    Just fun -> verScFunCall fun argsVals

verScFunCall :: Function -> [CallArg] -> VerRes Exp
verScFunCall (FunR name args ret stms) argsVals = do
  let expArgsVals = map (\(AExp exp) -> exp) argsVals
  addArgMap args expArgsVals
  let retVarIdent = Ident ((prismShowIdent name) ++ "_retVal")
  addReturnVar retVarIdent
  mapM_ verScStm stms
  removeReturnVar
  clearArgMap
  return (EVar retVarIdent)
--TODO: to jest przepisane z verScFunSendT


-- ScSendT --

verScSendT :: Ident -> [CallArg] -> VerRes ()
verScSendT funName argsVals = do
  world <- get
  case Map.lookup funName (funs world) of
    Just fun -> verScFunSendT fun argsVals

-- TODO: nie działają zagnieżdżone funkcje. 
-- Chyba musi być wielopoziomowy argMap
-- To jest wersja dla sendTransaction, dla call powinno być co innego
verScFunSendT :: Function -> [CallArg] -> VerRes ()
verScFunSendT (Fun name args stms) argsVals = do
  let expArgsVals = map (\(AExp exp) -> exp) (init argsVals)
  let (ABra sender value) = last argsVals
  addArgMap args expArgsVals
  addSender sender
  addValue value
  senderEval <- verScExp sender
  case senderEval of
    EStr str -> do
      when 
        (value /= (EInt 0)) 
        (do
          addAddress str
          balance <- getAddressBalance str
          transferToContract balance value)
      mapM_ verScStm stms
  removeValue
  removeSender
  clearArgMap

verScFunSendT (FunR name args ret stms) argsVals =
  verScFunSendT (Fun name args stms) argsVals


