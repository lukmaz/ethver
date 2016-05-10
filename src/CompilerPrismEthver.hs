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
  addContrGlobVar typ ident

verCoFun :: Function -> VerRes ()
verCoFun (Fun name args stms) = do
  --addFun fun
  world <- get
  -- TODO argumenty
  mapM_ addArg args
  -- TODO: czy tu musi być verCoStm?
  mapM_ verCoStm stms


addUser :: UserDecl -> VerRes ()
addUser (UDec name) = do
  addAddress name

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
-- CoStm --
-----------

verCoStm :: Stm -> VerRes ()
verCoStm (SExp exp) = do
  _ <- verCoExp exp
  return ()
  
verCoStm (SReturn exp) = do
  evalExp <- verCoExp exp
  world <- get
  _ <- verCoExp (EAss (head $ returnVar world) evalExp)
  return ()

-- TODO: drugi gracz
-- TODO: zrobić, żeby return wychodziło z wykonania bieżącej funkcji
verCoStm (SIf cond ifBlock) = do
  evalCond <- verCoExp cond
  world <- get
  -- TODO: P0
  let ifState = currState $ player0 world
  --TODO: P0
  addTransToNewStateP0
    ""
    [evalCond]
    []
  verCoStm ifBlock
  world <- get
  --TODO: P0
  addCustomTransP0
    ""
    ifState
    --TODO: P0
    (currState $ player0 world)
    [negateExp evalCond]
    []

-- TODO: drugi gracz, kontrakt
verCoStm (SIfElse cond ifBlock elseBlock) = do
  evalCond <- verCoExp cond
  world <- get
  -- TODO: P0
  let ifState = currState $ player0 world
  --TODO: P0
  addTransToNewStateP0
    ""
    [evalCond]
    []
  verCoStm ifBlock
  world <- get
  -- TODO: P0
  let endIfState = currState $ player0 world
  -- TODO: P0
  addCustomTransP0
    ""
    ifState
    -- TODO: P0
    (numStates (player0 world) + 1)
    [negateExp evalCond]
    []
  -- TODO: P0
  world <- get
  let newState = numStates (player0 world) + 1
  -- TODO: P0
  modifyPlayer0 (setCurrState newState)
  modifyPlayer0 (setNumStates newState)
  verCoStm elseBlock
  world <- get
  addCustomTransP0
    ""
    -- TODO: P0
    (currState $ player0 world)
    endIfState
    []
    []
  -- TODO: P0
  modifyPlayer0 (setCurrState endIfState)
  
verCoStm (SBlock stms) = do
  mapM_ verCoStm stms


-----------
-- CoExp --
-----------

-- TODO
verCoExp :: Exp -> VerRes Exp
verCoExp exp = verScExp exp

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

-- TODO: drugi gracz
-- TODO: zrobić, żeby return wychodziło z wykonania bieżącej funkcji
verScStm (SIf cond ifBlock) = do
  evalCond <- verScExp cond
  world <- get
  -- TODO: P0
  let ifState = currState $ player0 world
  --TODO: P0
  addTransToNewStateP0
    ""
    [evalCond]
    []
  verScStm ifBlock
  world <- get
  addCustomTransP0
    ""
    ifState
    -- TODO: P0
    (currState $ player0 world)
    [negateExp evalCond]
    []

-- TODO: drugi gracz, kontrakt
verScStm (SIfElse cond ifBlock elseBlock) = do
  evalCond <- verScExp cond
  world <- get
  -- TODO: P0
  let ifState = currState $ player0 world
  --TODO: P0
  addTransToNewStateP0
    ""
    [evalCond]
    []
  verScStm ifBlock
  world <- get
  -- TODO: P0
  let endIfState = currState $ player0 world
  addCustomTransP0
    ""
    ifState
    (numStates (player0 world) + 1)
    [negateExp evalCond]
    []
  world <- get
  -- TODO: P0
  let newState = numStates (player0 world) + 1
  modifyPlayer0 (setCurrState newState)
  modifyPlayer0 (setNumStates newState)
  verScStm elseBlock
  world <- get
  addCustomTransP0
    ""
    -- TODO: P0
    (currState $ player0 world)
    endIfState
    []
    []
  -- TODO: P0
  modifyPlayer0 (setCurrState endIfState)
  
verScStm (SBlock stms) = do
  mapM_ verScStm stms

-----------
-- Exp --
-----------

verScExp :: Exp -> VerRes Exp

verScExp (EEq exp1 exp2) = verScMathExp (EEq exp1 exp2)
verScExp (EAdd exp1 exp2) = verScMathExp (EAdd exp1 exp2)
verScExp (ESub exp1 exp2) = verScMathExp (ESub exp1 exp2)
verScExp (EMul exp1 exp2) = verScMathExp (EMul exp1 exp2)
verScExp (EDiv exp1 exp2) = verScMathExp (EDiv exp1 exp2)
verScExp (EMod exp1 exp2) = verScMathExp (EMod exp1 exp2)

verScExp (EAss ident exp) = verScValExp (EAss ident exp)
verScExp (EVar ident) = verScValExp (EVar ident)
verScExp EValue = verScValExp EValue
verScExp ESender = verScValExp ESender
verScExp (EInt x) = verScValExp (EInt x)
verScExp (EStr s) = verScValExp (EStr s)

verScExp (ECall idents exps) = verScCallExp (ECall idents exps)
verScExp (ESend receiver args) = verScCallExp (ESend receiver args)


-------------
-- MathExp --
-------------

verScMathExp (EEq exp1 exp2) = do
  evalExp1 <- verScExp exp1
  evalExp2 <- verScExp exp2
  return (EEq evalExp1 evalExp2)

verScMathExp (EAdd exp1 exp2) = do
  evalExp1 <- verScExp exp1
  evalExp2 <- verScExp exp2
  return (EAdd evalExp1 evalExp2)

verScMathExp (ESub exp1 exp2) = do
  evalExp1 <- verScExp exp1
  evalExp2 <- verScExp exp2
  return (ESub evalExp1 evalExp2)

verScMathExp (EMul exp1 exp2) = do
  evalExp1 <- verScExp exp1
  evalExp2 <- verScExp exp2
  return (EMul evalExp1 evalExp2)

verScMathExp (EDiv exp1 exp2) = do
  evalExp1 <- verScExp exp1
  evalExp2 <- verScExp exp2
  return (EDiv evalExp1 evalExp2)

verScMathExp (EMod exp1 exp2) = do
  evalExp1 <- verScExp exp1
  evalExp2 <- verScExp exp2
  return (EMod evalExp1 evalExp2)


------------
-- ValExp --
------------

-- TODO: automatyczna generacja standardowego przejścia na nast. stan
-- TODO: na razie tylko P0
verScValExp (EAss ident exp) = do
  evalExp <- verScExp exp
  world <- get
  minV <- minValue ident
  maxV <- maxValue ident
  --TODO: P0
  addTransToNewStateP0 
    ""
    [EGe evalExp (EInt minV), ELe evalExp (EInt maxV)]
    [(ident, evalExp)]
  return (EAss ident evalExp)

verScValExp (EVar ident) = do
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

verScValExp EValue = do
  return EValue

verScValExp ESender = do
  return ESender

verScValExp (EInt x) =
  return (EInt x)

verScValExp (EStr s) = do
  number <- getAddressNumber s
  addProps ("getAddress Number " ++ s ++ " = " ++ (show number) ++ "\n")
  return (EInt number)


----------------
-- CallExp --
----------------

-- TODO: na razie możemy mieć tylko jeden kontrakt
verScCallExp (ECall idents exps) = do
  case idents of
    [funName, (Ident "sendTransaction")] -> do 
      verScSendTAux funName exps
      return (ECall idents exps)
    [funName, (Ident "call")] -> do
      verScCallAux funName exps

verScCallExp (ESend receiverExp args) = do
  case args of
    [AExp val] -> do
      receiverEval <- verScExp receiverExp
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
verScCallAux :: Ident -> [CallArg] -> VerRes Exp
verScCallAux funName argsVals = do
  world <- get
  case Map.lookup funName (funs world) of
    Just fun -> verScFunCall fun argsVals

verScFunCall :: Function -> [CallArg] -> VerRes Exp
verScFunCall (FunR name args ret stms) argsVals = do
  let expArgsVals = map (\(AExp exp) -> exp) argsVals
  mapM_ addArgMap $ zip args expArgsVals
  let retVarIdent = Ident ((prismShowIdent name) ++ "_retVal")
  addReturnVar retVarIdent
  mapM_ verScStm stms
  removeReturnVar
  return (EVar retVarIdent)
--TODO: to jest przepisane z verScFunSendT


-- ScSendT --

verScSendTAux :: Ident -> [CallArg] -> VerRes ()
verScSendTAux funName argsVals = do
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
  mapM_ addArgMap $ zip args expArgsVals
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
      mapM_ verScStm stms
  --removeValue
  --removeSender

verScFunSendT (FunR name args ret stms) argsVals =
  verScFunSendT (Fun name args stms) argsVals


addArg :: Arg -> VerRes ()
addArg (Ar typ ident) = do
  -- TODO: sztywna nazwa "arg"
  addBcVar typ ident

addArgMap :: (Arg, Exp) -> VerRes ()
addArgMap ((Ar typ ident), exp) = do
  verScExp (EAss ident exp)
  return ()
