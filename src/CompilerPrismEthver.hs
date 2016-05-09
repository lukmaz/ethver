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
  addContrGlobVar typ ident

verCoFun :: Function -> VerRes ()
verCoFun (Fun name args stms) = do
  --addFun fun
  world <- get
  -- TODO argumenty
  -- mapM_ (addArg name) args
  -- TODO: czy tu musi być verCoStm?
  mapM_ verScStm stms



--------------
-- SCENARIO --
--------------

verScenario :: Scenario -> VerRes ()
verScenario (Scen decls stms) = do
  mapM_ verScDecl decls
  mapM_ verScStm stms

-- TODO: Drugi gracz
verScDecl :: Decl -> VerRes ()
verScDecl (Dec typ ident) = do
  addP0Var typ ident

-----------
-- ScStm --
-----------

verScStm :: Stm -> VerRes ()
verScStm (SExp exp) = do
  _ <- verExp exp
  return ()
  
verScStm (SReturn exp) = do
  evalExp <- verExp exp
  world <- get
  _ <- verExp (EAss (head $ returnVar world) evalExp)
  return ()

-- TODO: drugi gracz
-- TODO: zrobić, żeby return wychodziło z wykonania bieżącej funkcji
verScStm (SIf cond ifBlock) = do
  evalCond <- verExp cond
  world <- get
  let ifState = currStateP0 world
  addTransP0
    [evalCond]
    []
  verScStm ifBlock
  world <- get
  addCustomTransP0
    ifState
    (currStateP0 world)
    [negateExp evalCond]
    []

-- TODO: drugi gracz, kontrakt
verScStm (SIfElse cond ifBlock elseBlock) = do
  evalCond <- verExp cond
  world <- get
  let ifState = currStateP0 world
  addTransP0
    [evalCond]
    []
  verScStm ifBlock
  world <- get
  let endIfState = currStateP0 world
  addCustomTransP0
    ifState
    (numStatesP0 world + 1)
    [negateExp evalCond]
    []
  world <- get
  put (world {currStateP0 = numStatesP0 world + 1, numStatesP0 = numStatesP0 world + 1})
  verScStm elseBlock
  world <- get
  addCustomTransP0
    (currStateP0 world)
    endIfState
    []
    []
  world <- get
  put (world {currStateP0 = endIfState})
  
verScStm (SBlock stms) = do
  mapM_ verScStm stms

-----------
-- Exp --
-----------

verExp :: Exp -> VerRes Exp

verExp (EEq exp1 exp2) = verMathExp (EEq exp1 exp2)
verExp (EAdd exp1 exp2) = verMathExp (EAdd exp1 exp2)
verExp (ESub exp1 exp2) = verMathExp (ESub exp1 exp2)
verExp (EMul exp1 exp2) = verMathExp (EMul exp1 exp2)
verExp (EDiv exp1 exp2) = verMathExp (EDiv exp1 exp2)
verExp (EMod exp1 exp2) = verMathExp (EMod exp1 exp2)

verExp (EAss ident exp) = verValExp (EAss ident exp)
verExp (EVar ident) = verValExp (EVar ident)
verExp EValue = verValExp EValue
verExp ESender = verValExp ESender
verExp (EInt x) = verValExp (EInt x)
verExp (EStr s) = verValExp (EStr s)

verExp (ECall idents exps) = verCallExp (ECall idents exps)
verExp (ESend receiver args) = verCallExp (ESend receiver args)


-------------
-- MathExp --
-------------

verMathExp (EEq exp1 exp2) = do
  evalExp1 <- verExp exp1
  evalExp2 <- verExp exp2
  return (EEq evalExp1 evalExp2)

verMathExp (EAdd exp1 exp2) = do
  evalExp1 <- verExp exp1
  evalExp2 <- verExp exp2
  return (EAdd evalExp1 evalExp2)

verMathExp (ESub exp1 exp2) = do
  evalExp1 <- verExp exp1
  evalExp2 <- verExp exp2
  return (ESub evalExp1 evalExp2)

verMathExp (EMul exp1 exp2) = do
  evalExp1 <- verExp exp1
  evalExp2 <- verExp exp2
  return (EMul evalExp1 evalExp2)

verMathExp (EDiv exp1 exp2) = do
  evalExp1 <- verExp exp1
  evalExp2 <- verExp exp2
  return (EDiv evalExp1 evalExp2)

verMathExp (EMod exp1 exp2) = do
  evalExp1 <- verExp exp1
  evalExp2 <- verExp exp2
  return (EMod evalExp1 evalExp2)


------------
-- ValExp --
------------

-- TODO: automatyczna generacja standardowego przejścia na nast. stan
-- TODO: na razie tylko P0
verValExp (EAss ident exp) = do
  evalExp <- verExp exp
  world <- get
  minV <- minValue ident
  maxV <- maxValue ident
  addTransP0 
    [EGe evalExp (EInt minV), ELe evalExp (EInt maxV)]
    [(ident, evalExp)]
  return (EAss ident evalExp)

verValExp (EVar ident) = do
  world <- get
  case Map.lookup ident (contrGlobVars world) of
    Just exp ->
      return (EVar ident)
    Nothing ->
      case Map.lookup ident (contrLocVars world) of
        Just exp ->
          return (EVar ident)
        Nothing ->
          case Map.lookup ident (p0Vars world) of
            Just exp ->
              return (EVar ident)
            Nothing ->
              case Map.lookup ident (p1Vars world) of
                Just exp ->
                  return (EVar ident)

verValExp EValue = do
  value <- getValue
  verExp value

verValExp ESender = do
  sender <- getSender
  verExp sender

verValExp (EInt x) =
  return (EInt x)

verValExp (EStr s) = do
  number <- getAddressNumber s
  return (EInt number)


----------------
-- CallExp --
----------------

-- TODO: na razie możemy mieć tylko jeden kontrakt
verCallExp (ECall idents exps) = do
  case idents of
    [funName, (Ident "sendTransaction")] -> do 
      verSendTAux funName exps
      return (ECall idents exps)
    [funName, (Ident "call")] -> do
      verCallAux funName exps

verCallExp (ESend receiverExp args) = do
  case args of
    [AExp val] -> do
      receiverEval <- verExp receiverExp
      case receiverEval of
        EStr receiverAddress -> do
          receiverNumber <- getAddressNumber receiverAddress
          receiverBalance <- getNumberBalance receiverNumber
          transferFromContract receiverBalance val
        EInt receiverNumber -> do
          receiverBalance <- getNumberBalance receiverNumber
          transferFromContract receiverBalance val
  return (ESend receiverExp args)


-- Call --

-- TODO: chyba powinno być najpierw kopiowanie coVars i scVars (?) na lokalne
verCallAux :: Ident -> [CallArg] -> VerRes Exp
verCallAux funName argsVals = do
  world <- get
  case Map.lookup funName (funs world) of
    Just fun -> verFunCall fun argsVals

verFunCall :: Function -> [CallArg] -> VerRes Exp
verFunCall (FunR name args ret stms) argsVals = do
  let expArgsVals = map (\(AExp exp) -> exp) argsVals
  mapM_ addArg $ zip args expArgsVals
  let retVarIdent = Ident ((prismShowIdent name) ++ "_retVal")
  addReturnVar retVarIdent
  mapM_ verScStm stms
  removeReturnVar
  return (EVar retVarIdent)
--TODO: to jest przepisane z verScFunSendT


-- ScSendT --

verSendTAux :: Ident -> [CallArg] -> VerRes ()
verSendTAux funName argsVals = do
  world <- get
  case Map.lookup funName (funs world) of
    Just fun -> verFunSendT fun argsVals

-- TODO: nie działają zagnieżdżone funkcje. 
-- Chyba musi być wielopoziomowy argMap
-- To jest wersja dla sendTransaction, dla call powinno być co innego
verFunSendT :: Function -> [CallArg] -> VerRes ()
verFunSendT (Fun name args stms) argsVals = do
  let expArgsVals = map (\(AExp exp) -> exp) (init argsVals)
  let (ABra sender value) = last argsVals
  mapM_ addArg $ zip args expArgsVals
  addSender sender
  addValue value
  case sender of
    EStr str -> do
      addAddress str
      when 
        (value /= (EInt 0)) 
        (do
          number <- getAddressNumber str
          balance <- getNumberBalance number
          transferToContract balance value)
      mapM_ verScStm stms
  removeValue
  removeSender

verFunSendT (FunR name args ret stms) argsVals =
  verFunSendT (Fun name args stms) argsVals


addArg :: (Arg, Exp) -> VerRes ()
addArg (_, exp) = do
  -- TODO: sztywna nazwa "arg"
  verExp (EAss (Ident "arg") exp)
  return ()
