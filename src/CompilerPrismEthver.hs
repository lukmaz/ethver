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
verProgram (Prog contract scenarios) = do
  verContract contract
  verScenarios scenarios
  addAdversarialTranss contract

addAdversarialTranss :: Contract -> VerRes ()
addAdversarialTranss (Contr _ _ _ funs) = do
  mapM_ (addAdversarialTranssToPlayer modifyPlayer0) funs
  mapM_ (addAdversarialTranssToPlayer modifyPlayer1) funs

--------------
-- CONTRACT --
--------------

verContract :: Contract -> VerRes ()
verContract (Contr name users decls funs) = do
  mapM_ addUser users
  mapM_ verCoDecl decls
  
  mapM_ (verFunBroadcast modifyPlayer0) funs
  mapM_ (verFunExecute modifyPlayer0) funs
  mapM_ (verFunBroadcast modifyPlayer1) funs
  mapM_ (verFunExecute modifyPlayer1) funs

  verExecTransaction modifyPlayer0
  verExecTransaction modifyPlayer1

  mapM_ verFunContract funs

-- TODO: globalne, nieglobalne
verCoDecl :: Decl -> VerRes ()
verCoDecl (Dec typ ident) = do
  addContrVar typ ident

verFunBroadcast :: ModifyModuleType -> Function -> VerRes ()
verFunBroadcast modifyModule (Fun name args stms) = do
  --TODO: argumenty
  mod <- modifyModule id
  addTransNoState
    modifyBlockchain 
    ("broadcast_" ++ (prismShowIdent name) ++ (show $ number mod))
    [
      EEq (EVar (Ident "cstate")) (EInt 1), 
      ENe (EVar $ Ident $ prismShowIdent name ++ "_state" ++ (show $ number mod)) (EVar $ Ident "T_BROADCAST")
    ]
    [[(Ident $ prismShowIdent name ++ "_state" ++ (show $ number mod), EVar (Ident "T_BROADCAST"))]]

verFunExecute :: ModifyModuleType -> Function -> VerRes ()
verFunExecute modifyModule (Fun name args stms) = do
  --TODO: argumenty
  mod <- modifyModule id

  let updates0 = [[(Ident "sender", EInt $ number mod), (Ident "val", EVar $ Ident $ prismShowIdent name ++ "_val" ++ (show $ number mod)), (Ident $ prismShowIdent name ++ "_state" ++ (show $ number mod), EVar (Ident "T_EXECUTED"))]]
  let addAssignment acc (Ar _ (Ident varName)) = acc ++ [(Ident $ prismShowIdent name ++ "_" ++ varName, EVar $Ident $ prismShowIdent name ++ "_" ++ varName ++ (show $ number mod))]
  let updates = [foldl addAssignment (head updates0) args]

  addTransNoState
    modifyBlockchain 
    ("broadcast_" ++ (prismShowIdent name))
    [
      EEq (EVar (Ident "cstate")) (EInt 1),
      EEq 
        (EVar $ Ident $ prismShowIdent name ++ "_state" ++ (show $ number mod)) 
        (EVar $ Ident "T_BROADCAST"),
      ELe 
        (EVar $ Ident $ prismShowIdent name ++ "_val" ++ (show $ number mod)) 
        (EVar $ Ident $ "balance" ++ (show $ number mod))
    ]
    updates

  addTransNoState
    modifyBlockchain 
    ""
    [
      EEq (EVar (Ident "cstate")) (EInt 1),
      EEq 
        (EVar $ Ident $ prismShowIdent name ++ "_state" ++ (show $ number mod)) 
        (EVar $ Ident "T_BROADCAST"),
      EGt 
        (EVar $ Ident $ prismShowIdent name ++ "_val" ++ (show $ number mod)) 
        (EVar $ Ident $ "balance" ++ (show $ number mod))
    ]
    [
      [(Ident $ prismShowIdent name ++ "_state" ++ (show $ number mod), EVar (Ident "T_INVALIDATED"))]
    ]

verFunContract :: Function -> VerRes ()
verFunContract (Fun name args stms) = do
  addFun (Fun name args stms)
  addBcVar (TUInt 4) $ Ident $ prismShowIdent name ++ "_state0" 
  addBcVar (TUInt 4) $ Ident $ prismShowIdent name ++ "_state1"

  -- adds also to argMap
  mapM_ (addArgument name) args

  -- TODO: skąd wziąć zakres val?
  addP0Var (TUInt 3) $ Ident $ prismShowIdent name ++ "_val0"
  addP1Var (TUInt 3) $ Ident $ prismShowIdent name ++ "_val1"

  mod <- modifyContract id
  addCustomTrans
    modifyContract
    ("broadcast_" ++ (prismShowIdent name))
    1
    0
    []
    [[(Ident "next_state", EInt $ numStates mod + 1)]]
  
  modifyContract (\mod -> mod {currState = numStates mod + 1, numStates = numStates mod + 1})
  
  mapM_ (verStm modifyContract) stms

  mod <- modifyContract id
  addCustomTrans
    modifyContract
    ""
    (numStates mod)
    1
    []
    [[]]
  
  clearArgMap

verExecTransaction :: ModifyModuleType -> VerRes ()
verExecTransaction modifyModule = do
  mod <- modifyModule id
  addTransNoState
    modifyContract
    ""
    [
      EEq (EVar $ Ident "cstate") (EInt 0),
      EEq (EVar $ Ident "sender") (EInt $ number mod),
      EGe (EVar $ Ident $ "balance" ++ (show $ number mod)) (EVar $ Ident "val"),
      ELe (EAdd (EVar $ Ident "contract_balance") (EVar $ Ident "val")) (EVar $ Ident "MAX_CONTRACT_BALANCE")
    ]
    [[
      (Ident "cstate", EVar $ Ident "next_state"),
      (Ident $ "balance" ++ (show $ number mod), 
        ESub (EVar $ Ident $ "balance" ++ (show $ number mod)) (EVar $ Ident "val")),
      (Ident "contract_balance",
        EAdd (EVar $ Ident "contract_balance") (EVar $ Ident "val"))
    ]]


addUser :: UserDecl -> VerRes ()
addUser (UDec name) = do
  addPlayer name

addAdversarialTranssToPlayer :: ModifyModuleType -> Function -> VerRes ()
addAdversarialTranssToPlayer modifyModule (Fun (Ident funName) args _) = do
  mod <- modifyModule id 
  let valName = Ident $ funName ++ "_val" ++ (show $ number mod)
  maxVal <- maxValue valName
  let maxValsList = generateValsList maxVal args
  forM_ 
    maxValsList
    (\vals -> addTransNoState
      modifyModule
      ("broadcast_" ++ funName ++ (show $ number mod))
      [
        ENot $ EVar $ Ident $ "critical_section" ++ (show $ 1 - (number mod)),
        EEq (EVar $ Ident "cstate") (EInt 1),
        EEq (EVar $ Ident $ "state" ++ (show $ number mod)) (EInt (-1))
      ]
      (advUpdates (number mod) funName args vals)
    )

generateValsList :: Integer -> [Arg] -> [[Integer]]
generateValsList maxVal args = 
  let maxVals = maxVal:(map (\(Ar typ _) -> maxValueOfType typ) args) in
    generateAllVals maxVals

generateAllVals :: [Integer] -> [[Integer]]
generateAllVals [] = []

generateAllVals [h] =
  map (\a -> [a]) [0..h]

generateAllVals (h:t) = 
  let vt = generateAllVals t in
    foldl
      (\acc x -> 
        (map (\v -> x:v) vt)
          ++ acc)
      []
      (reverse [0..h])

advUpdates :: Integer -> String -> [Arg] -> [Integer] -> [[(Ident, Exp)]]
advUpdates number funName args valList =
  let varNames = "val":(map (\(Ar _ (Ident ident)) -> ident) args) in
    [
      map
        (\(varName, v) -> (Ident $ funName ++ "_" ++ varName ++ (show number), EInt v))
        (zip varNames valList)
    ]

--------------
-- SCENARIO --
--------------

verScenarios :: [Scenario] -> VerRes ()
verScenarios [(Scen userName0 decls0 stms0), (Scen userName1 decls1 stms1)] = do
  --TODO: przepadają userName'y
  verScenario modifyPlayer0 decls0 stms0
  verScenario modifyPlayer1 decls1 stms1

verScenario :: ModifyModuleType -> [Decl] -> [Stm] -> VerRes ()
verScenario modifyModule decls stms = do
  mod <- modifyModule id

  mapM_ (verDecl modifyModule) decls

  mapM_ (verStm modifyModule) stms

  -- add critical sections stuff 
  _ <- modifyModule addCS
  
  addFirstCustomTrans
    modifyModule
    ""
    0
    1
    [ENe (EVar $ Ident "ADVERSARY") (EInt $ number mod)]
    [[]]

  addCustomTrans
    modifyModule
    ""
    0
    (-1)
    [EEq (EVar $ Ident "ADVERSARY") (EInt $ number mod)]
    [[]]


verDecl :: ModifyModuleType -> Decl -> VerRes ()
verDecl modifyModule (Dec typ ident) = do
  addVar modifyModule typ ident


---------
-- Stm --
---------

verStm :: ModifyModuleType -> Stm -> VerRes ()
verStm modifyModule (SExp exp) = do
  _ <- verExp modifyModule exp
  return ()
  
verStm modifyModule (SReturn exp) = do
  evalExp <- verExp modifyModule exp
  world <- get
  _ <- verExp modifyModule (EAss (head $ returnVar world) evalExp)
  return ()

-- TODO: zrobić, żeby return wychodziło z wykonania bieżącej funkcji
verStm modifyModule (SIf cond ifBlock) = do
  evalCond <- verExp modifyModule cond
  mod <- modifyModule id
  let ifState = currState mod
  addTransToNewState
    modifyModule
    ""
    [evalCond]
    [[]]
  verStm modifyModule ifBlock
  mod <- modifyModule id
  addCustomTrans
    modifyModule
    ""
    ifState
    (currState mod)
    [negateExp evalCond]
    [[]]

verStm modifyModule (SIfElse cond ifBlock elseBlock) = do
  evalCond <- verExp modifyModule cond
  mod <- modifyModule id
  let ifState = currState mod
  addTransToNewState
    modifyModule
    ""
    [evalCond]
    [[]]
  verStm modifyModule ifBlock
  mod <- modifyModule id
  let endIfState = currState mod 
  addCustomTrans
    modifyModule
    ""
    ifState
    (numStates mod + 1)
    [negateExp evalCond]
    [[]]
  mod <- modifyModule id
  let newState = numStates mod + 1
  modifyModule (setCurrState newState)
  modifyModule (setNumStates newState)
  verStm modifyModule elseBlock
  mod <- modifyModule id
  addCustomTrans
    modifyModule
    ""
    (currState mod)
    endIfState
    []
    [[]]
  _ <- modifyModule (setCurrState endIfState)
  return ()
  
verStm modifyModule (SBlock stms) = do
  mapM_ (verStm modifyModule) stms


-----------
-- Exp --
-----------

verExp :: ModifyModuleType -> Exp -> VerRes Exp

verExp modifyModule (EEq exp1 exp2) = verMathExp modifyModule (EEq exp1 exp2)
verExp modifyModule (ENe exp1 exp2) = verMathExp modifyModule (ENe exp1 exp2)
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

verMathExp modifyModule (ENe exp1 exp2) = do
  evalExp1 <- verExp modifyModule exp1
  evalExp2 <- verExp modifyModule exp2
  return (ENe evalExp1 evalExp2)

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
  minV <- minValue ident
  maxV <- maxValue ident
  addTransToNewState
    modifyModule
    ""
    [EGe evalExp (EInt minV), ELe evalExp (EInt maxV)]
    [[(ident, evalExp)]]
  return (EAss ident evalExp)

verValExp modifyModule (EVar ident) = do
  world <- get
  case Map.lookup ident $ argMap world of
    Just varName -> return (EVar varName)
    Nothing -> return (EVar ident)

verValExp modifyModule EValue = do
  return EValue

verValExp modifyModule ESender = do
  return ESender

verValExp modifyModule (EInt x) =
  return (EInt x)

verValExp modifyModule (EStr s) = do
  number <- getPlayerNumber s
  return (EInt number)


----------------
-- CallExp --
----------------

-- TODO: na razie możemy mieć tylko jeden kontrakt
verCallExp :: ModifyModuleType -> Exp -> VerRes Exp

verCallExp modifyModule (ECall idents args) = do
  case idents of
    [funName, (Ident "sendTransaction")] -> do 
      verSendTAux modifyModule funName args
      return (ECall idents args)
    [funName, (Ident "call")] -> do
      verCallAux modifyModule funName args
    [Ident "random"] -> do
      verRandom modifyModule args


verCallExp modifyModule (ESend receiverExp args) = do
  case args of
    [AExp arg] -> do
      val <- verExp modifyModule arg
      case receiverExp of
        ESender -> do
          verStm 
            modifyModule 
            (SIf 
              (EEq (EVar $ Ident "sender") (EInt 0))
              (SExp $ ESend (EInt 0) args)
            )
          verStm
            modifyModule
            (SIf
              (EEq (EVar $ Ident "sender") (EInt 1))
              (SExp $ ESend (EInt 1) args)
            )
        EStr receiverAddress -> do
          receiverNumber <- getPlayerNumber receiverAddress
          let receiverBalance = Ident $ "balance" ++ (show receiverNumber) 
          transferFromContract receiverBalance val
        EInt receiverNumber -> do
          let receiverBalance = Ident $ "balance" ++ (show receiverNumber)
          transferFromContract receiverBalance val
  return (ESend receiverExp args)

-----------------------------
-- Call auxilary functions --
-----------------------------

verRandom :: ModifyModuleType -> [CallArg] -> VerRes Exp
verRandom modifyModule [AExp (EInt range)] = do
  mod <- modifyModule id
  let localVarName = "local" ++ (show $ numLocals mod)
  addLocal modifyModule (TUInt range)
  addTransToNewState 
    modifyModule 
    ""
    []
    (foldl
      (\acc x -> acc ++ [[(Ident localVarName, EInt x)]])
      []
      [0..(range - 1)]
    )
  return (EVar $ Ident localVarName)

-- TODO: chyba powinno być najpierw kopiowanie coVars i scVars (?) na lokalne
verCallAux :: ModifyModuleType -> Ident -> [CallArg] -> VerRes Exp
verCallAux modifyModule funName argsVals = do
  -- TODO: stara wersja, przepisać jak sendT
  world <- get
  case Map.lookup funName (funs world) of
    Just fun -> verFunCall modifyModule fun argsVals

verFunCall :: ModifyModuleType -> Function -> [CallArg] -> VerRes Exp
verFunCall modifyModule (FunR name args ret stms) argsVals = do
  -- TODO: stara wersja, przepisać jak sendT
  let expArgsVals = map (\(AExp exp) -> exp) argsVals
  --mapM_ (addArgMap modifyModule) $ zip args expArgsVals
  let retVarIdent = Ident ((prismShowIdent name) ++ "_retVal")
  addReturnVar retVarIdent
  mapM_ (verStm modifyModule) stms
  removeReturnVar
  return (EVar retVarIdent)
--TODO: to jest przepisane z verScFunSendT


-- ScSendT --

verSendTAux :: ModifyModuleType -> Ident -> [CallArg] -> VerRes ()
verSendTAux modifyModule funName argsVals = do
  world <- get
  mod <- modifyModule id
  case Map.lookup funName (funs world) of
    Just fun -> do
      let argNames = getArgNames fun
      let expArgsVals = map (\(AExp exp) -> exp) (init argsVals)
      -- TODO: olewamy "from", bo sender jest wiadomy ze scenariusza
      let (ABra _ value) = last argsVals
      
      let updates0 = [[(Ident $ (prismShowIdent funName) ++ "_val" ++ (show $ number mod), value)]]
      let addAssignment acc (argName, argVal) = acc ++ [createAssignment (number mod) funName argName argVal]
      let updates = [foldl addAssignment (head updates0) $ zip argNames expArgsVals]
      

      addTransToNewState 
        modifyModule 
        ("broadcast_" ++ (prismShowIdent funName) ++ (show $ number mod)) 
        [EEq (EVar (Ident "cstate")) (EInt 1)]
        updates

      addTransToNewState
        modifyModule
        ""
        [EEq (EVar (Ident "cstate")) (EInt 1), 
          EEq 
            (EVar (Ident (prismShowIdent funName ++ "_state" ++ (show $ number mod)))) 
            (EVar (Ident "T_EXECUTED"))]
        [[]]

getArgNames :: Function -> [Arg]
getArgNames (Fun _ args _) = args
getArgNames (FunR _ args _ _) = args

createAssignment :: Integer -> Ident -> Arg -> Exp -> (Ident, Exp)
createAssignment playerNumber funName (Ar _ (Ident varName)) exp = 
  (Ident $ prismShowIdent funName ++ "_" ++ varName ++ (show playerNumber), exp)

{-
addArgMap :: ModifyModuleType -> (Arg, Exp) -> VerRes ()
addArgMap modifyModule ((Ar typ ident), exp) = do
  verExp modifyModule (EAss ident exp)
  return ()
-}
