module ExpPrismEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import AbsEthver
import AuxPrismEthver
import AuxWorldPrismEthver
import CodePrismEthver
import ConstantsEthver
import WorldPrismEthver

---------
-- Stm --
---------

verStm :: ModifyModuleType -> Stm -> VerRes ()

verStm modifyModule (SAss ident exp) = 
  verFullAss modifyModule (SAss ident exp)

verStm modifyModule (SArrAss ident index exp) =
  verFullAss modifyModule (SArrAss ident index exp)

verStm modifyModule (SReturn exp) = do
  evalExp <- verExp modifyModule exp 
  world <- get 
  verStm modifyModule (SAss (head $ returnVar world) evalExp)

-- TODO: zrobić, żeby return wychodziło z wykonania bieżącej funkcji
verStm modifyModule (SIf cond ifBlock) = do
  evalCond <- verExp modifyModule cond
  mod <- modifyModule id
  let ifState = currState mod 
  addTransToNewState
    modifyModule
    ""  
    [evalCond]
    -- TODO: Alive?
    [([], [Alive])]
  verStm modifyModule ifBlock
  mod <- modifyModule id
  addCustomTrans
    modifyModule
    ""  
    ifState
    (currState mod)
    [negateExp evalCond]
    -- TODO: Alive?
    [([], [Alive])]

verStm modifyModule (SIfElse cond ifBlock elseBlock) = do
  evalCond <- verExp modifyModule cond
  mod <- modifyModule id
  let ifState = currState mod 
  addTransToNewState
    modifyModule
    ""  
    [evalCond]
    -- TODO: Alive?
    [([], [Alive])]
  verStm modifyModule ifBlock
  mod <- modifyModule id
  let endIfState = currState mod 
  addCustomTrans
    modifyModule
    ""  
    ifState
    (numStates mod + 1)
    [negateExp evalCond]
    -- TODO: Alive?
    [([], [Alive])]
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
    -- TODO: Alive?
    [([], [Alive])]
  _ <- modifyModule (setCurrState endIfState)
  return ()

verStm modifyModule (SWhile cond whileBlock) = do
  evalCond <- verExp modifyModule cond
  mod <- modifyModule id

  let
    breakState = (currState mod) + 1
    whileState = (currState mod) + 2

  addCustomTrans 
    modifyModule
    ""
    (currState mod)
    whileState
    []
    -- TODO: Alive?
    [([], [Alive])]

  modifyModule (setCurrState whileState)
  modifyModule (setNumStates whileState)

  modifyModule $ addBreakState breakState

  addTransToNewState
    modifyModule
    ""  
    [evalCond]
    -- TODO: Alive?
    [([], [Alive])]

  verStm modifyModule whileBlock
  mod <- modifyModule id

  -- go to begin of a loop
  addCustomTrans
    modifyModule
    ""
    (currState mod)
    whileState
    []
    -- TODO: Alive?
    [([], [Alive])]

  mod <- modifyModule id

  -- end of a loop
  addCustomTrans
    modifyModule
    ""  
    whileState
    (numStates mod + 1)
    [negateExp evalCond]
    -- TODO: Alive?
    [([], [Alive])]

  -- escape from breakState
  addCustomTrans
    modifyModule
    ""
    breakState
    (numStates mod + 1)
    []
    -- TODO: Alive?
    [([], [Alive])]

  mod <- modifyModule id
  let newState = numStates mod + 1
  modifyModule (setCurrState newState)
  modifyModule (setNumStates newState)

  modifyModule removeBreakState

  return ()

verStm modifyModule (SBreak) = do
  mod <- modifyModule id
  addCustomTrans
    modifyModule
    ""
    (currState mod)
    (head $ breakStates mod)
    []
    -- TODO: Alive?
    [([], [Alive])]

  mod <- modifyModule id
  let newState = numStates mod + 1
  modifyModule (setCurrState newState)
  modifyModule (setNumStates newState)
  return ()

verStm modifyModule (SBlock stms) = do
  mapM_ (verStm modifyModule) stms

verStm modifyModule (SSend receiverExp arg) = do
  val <- verExp modifyModule arg
  mod <- modifyModule id
  let actualSender = whichSender mod
  case receiverExp of
    ESender -> do
      verStm 
        modifyModule 
        (SIf 
          (EEq (EVar actualSender) (EInt 0))
          (SSend (EInt 0) arg)
        )
      verStm
        modifyModule
        (SIf
          (EEq (EVar actualSender) (EInt 1))
          (SSend (EInt 1) arg)
        )
    EStr receiverAddress -> do
      receiverNumber <- getPlayerNumber receiverAddress
      let receiverBalance = Ident $ sBalancePrefix ++ (show receiverNumber) 
      transferFromContract receiverBalance val
    EInt receiverNumber -> do
      let receiverBalance = Ident $ sBalancePrefix ++ (show receiverNumber)
      transferFromContract receiverBalance val

verStm modifyModule (SSendT funIdent args) = do
  verSendTAux modifyModule funIdent args

verStm modifyModule (SSendC funIdent args) = do
  verSendCAux modifyModule funIdent args

verStm modifyModule (SWait cond) = do
  evalCond <- verExp modifyModule cond
  addTransToNewState
    modifyModule
    ""
    [EOr evalCond $ EVar $ Ident sTimelocksReleased]
    -- TODO: Alive?
    [([], [Alive])]


---------
-- Ass --
---------

verFullAss :: ModifyModuleType -> Stm -> VerRes ()

verFullAss modifyModule (SAss ident exp) = do
  case exp of
    ERandL (EInt _) ->
      addLazyRandom ident
    _ -> 
      return ()

  (guards, updates) <- generateSimpleAss modifyModule (SAss ident exp)
  
  addTransToNewState
    modifyModule
    ""
    guards
    -- TODO: Alive?
    [(updates, [Alive])]

verFullAss modifyModule (SArrAss (Ident ident) index exp) = do
  case index of
    ESender -> do
      mod <- modifyModule id
      let actualSender = whichSender mod
      verStm 
        modifyModule 
        (SIf 
          (EEq (EVar actualSender) (EInt 0))
          (SAss (Ident $ ident ++ "_0") exp)
        )
      verStm
        modifyModule
        (SIf
          (EEq (EVar actualSender) (EInt 1))
          (SAss (Ident $ ident ++ "_1") exp)
        )
    EVar v -> do
      var <- verExp modifyModule (EVar v)
      verStm 
        modifyModule 
        (SIf 
          (EEq var (EInt 0))
          (SAss (Ident $ ident ++ "_0") exp)
        )
      verStm
        modifyModule
        (SIf
          (EEq var (EInt 1))
          (SAss (Ident $ ident ++ "_1") exp)
        )
    EStr indexAddress -> do
      indexNumber <- getPlayerNumber indexAddress
      let indexVar = Ident $ ident ++ "_" ++ (show indexNumber)
      verStm modifyModule $ SAss indexVar exp
    EInt indexNumber -> do
      let indexVar = Ident $ ident ++ "_" ++ (show indexNumber)
      verStm modifyModule $ SAss indexVar exp

-- generateSimpleAss

-- returns simple updates [], not [[]]
generateSimpleAss :: ModifyModuleType -> Stm -> VerRes ([Exp], [(Ident, Exp)])
generateSimpleAss modifyModule (SAss ident exp) = do
  evalExp <- verExp modifyModule exp 
  typ <- findVarType ident
  minV <- minValue ident
  maxV <- maxTypeValue ident
  let guards = case typ of Just TBool -> []
                           Just _ -> [EGe evalExp (EInt minV), ELe evalExp (EInt maxV)]
  return (guards, [(ident, evalExp)])

generateSimpleAss modifyModule (SArrAss (Ident ident) index exp) = do
  case index of
    -- TODO: ESender (zmienić też verFullAss)
    EStr indexAddress -> do
      indexNumber <- getPlayerNumber indexAddress
      let indexVar = Ident $ ident ++ "_" ++ (show indexNumber)
      generateSimpleAss modifyModule $ SAss indexVar exp 
    EInt indexNumber -> do
      let indexVar = Ident $ ident ++ "_" ++ (show indexNumber)
      generateSimpleAss modifyModule $ SAss indexVar exp 


---------
-- Exp --
---------

verExp :: ModifyModuleType -> Exp -> VerRes Exp

verExp modifyModule (ENot exp) = verMathExp modifyModule (ENot exp)
verExp modifyModule (ENeg exp) = verMathExp modifyModule (ENeg exp)
verExp modifyModule (EAnd exp1 exp2) = verMathExp modifyModule (EAnd exp1 exp2)
verExp modifyModule (EOr exp1 exp2) = verMathExp modifyModule (EOr exp1 exp2)
verExp modifyModule (EEq exp1 exp2) = verMathExp modifyModule (EEq exp1 exp2)
verExp modifyModule (ENe exp1 exp2) = verMathExp modifyModule (ENe exp1 exp2)
verExp modifyModule (ELt exp1 exp2) = verMathExp modifyModule (ELt exp1 exp2)
verExp modifyModule (ELe exp1 exp2) = verMathExp modifyModule (ELe exp1 exp2)
verExp modifyModule (EGt exp1 exp2) = verMathExp modifyModule (EGt exp1 exp2)
verExp modifyModule (EGe exp1 exp2) = verMathExp modifyModule (EGe exp1 exp2)
verExp modifyModule (EAdd exp1 exp2) = verMathExp modifyModule (EAdd exp1 exp2)
verExp modifyModule (ESub exp1 exp2) = verMathExp modifyModule (ESub exp1 exp2)
verExp modifyModule (EMul exp1 exp2) = verMathExp modifyModule (EMul exp1 exp2)
verExp modifyModule (EDiv exp1 exp2) = verMathExp modifyModule (EDiv exp1 exp2)
verExp modifyModule (EMod exp1 exp2) = verMathExp modifyModule (EMod exp1 exp2)

verExp modifyModule (EVar ident) = verValExp modifyModule (EVar ident)
verExp modifyModule (EArray ident exp) = verValExp modifyModule (EArray ident exp)
verExp modifyModule EValue = verValExp modifyModule EValue
verExp modifyModule ESender = verValExp modifyModule ESender
verExp modifyModule (EInt x) = verValExp modifyModule (EInt x)
verExp modifyModule (EStr s) = verValExp modifyModule (EStr s)
verExp modifyModule ETrue = verValExp modifyModule ETrue
verExp modifyModule EFalse = verValExp modifyModule EFalse

verExp modifyModule (ERand exp) = verRandom modifyModule exp
verExp modifyModule (ERandL exp) = verRandomLazy modifyModule exp

-------------
-- MathExp --
-------------

verMathExp :: ModifyModuleType -> Exp -> VerRes Exp

verMathExp modifyModule (ENot exp) = do
  evalExp <- verExp modifyModule exp
  return (ENot evalExp)

verMathExp modifyModule (ENeg exp) = do
  evalExp <- verExp modifyModule exp
  return (ENeg evalExp)

verMathExp modifyModule (EEq exp1 exp2) = do
  evalExp1 <- verExp modifyModule exp1
  evalExp2 <- verExp modifyModule exp2
  return (EEq evalExp1 evalExp2)

verMathExp modifyModule (ENe exp1 exp2) = do
  evalExp1 <- verExp modifyModule exp1
  evalExp2 <- verExp modifyModule exp2
  return (ENe evalExp1 evalExp2)

verMathExp modifyModule (ELt exp1 exp2) = do
  evalExp1 <- verExp modifyModule exp1
  evalExp2 <- verExp modifyModule exp2
  return (ELt evalExp1 evalExp2)

verMathExp modifyModule (ELe exp1 exp2) = do
  evalExp1 <- verExp modifyModule exp1
  evalExp2 <- verExp modifyModule exp2
  return (ELe evalExp1 evalExp2)

verMathExp modifyModule (EGt exp1 exp2) = do
  evalExp1 <- verExp modifyModule exp1
  evalExp2 <- verExp modifyModule exp2
  return (EGt evalExp1 evalExp2)

verMathExp modifyModule (EGe exp1 exp2) = do
  evalExp1 <- verExp modifyModule exp1
  evalExp2 <- verExp modifyModule exp2
  return (EGe evalExp1 evalExp2)

verMathExp modifyModule (EAnd exp1 exp2) = do
  evalExp1 <- verExp modifyModule exp1
  evalExp2 <- verExp modifyModule exp2
  return (EAnd evalExp1 evalExp2)

verMathExp modifyModule (EOr exp1 exp2) = do
  evalExp1 <- verExp modifyModule exp1
  evalExp2 <- verExp modifyModule exp2
  return (EOr evalExp1 evalExp2)

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

verValExp modifyModule (EVar ident) = do
  world <- get
  typ <- findVarType ident
  case typ of
    Just (TRUInt range) -> do
      if Set.member ident (lazyRandoms world)
        then do
          removeLazyRandom ident
          verRandom modifyModule $ EInt range
        else do
          return (EVar ident)
    _ ->
      return (EVar ident)

verValExp modifyModule (EArray (Ident ident) index) = do
  mod <- modifyModule id
  let localVarName = (moduleName mod) ++ sLocalSuffix ++ (show $ numLocals mod)
  -- TODO: liczba graczy = 2
  maybeType <- findVarType $ Ident $ ident ++ "_0"
  
  case index of
    ESender -> do
      -- TODO: not needed anymore?
      error $ "verValExp: array[msg.sender] should not be used in scenarios (only in contract and comm)."
      {-
      case maybeType of
        Just typ -> do 
          addLocal modifyModule typ
          mod <- modifyModule id
          let actualSender = whichSender mod
          verStm 
            modifyModule 
            (SIf 
              (EEq (EVar actualSender) (EInt 0))
              (SAsses [AAss (Ident $ localVarName) (EVar $ Ident $ ident ++ "_0")])
            )
          verStm
            modifyModule
            (SIf
              (EEq (EVar actualSender) (EInt 1))
              (SAsses [AAss (Ident $ localVarName) (EVar $ Ident $ ident ++ "_1")])
            )
          return $ EVar $ Ident localVarName
      -}
    EVar v -> do
      case maybeType of
        Just typ -> do
          addLocal modifyModule typ
          var <- verExp modifyModule (EVar v)
          verStm 
            modifyModule 
            (SIf 
              (EEq var (EInt 0))
              (SAss (Ident $ localVarName) (EVar $ Ident $ ident ++ "_0"))
            )
          verStm
            modifyModule
            (SIf
              (EEq var (EInt 1))
              (SAss (Ident $ localVarName) (EVar $ Ident $ ident ++ "_1"))
            )
          return $ EVar $ Ident localVarName
    EStr indexAddress -> do
      indexNumber <- getPlayerNumber indexAddress
      let indexVar = Ident $ ident ++ "_" ++ (show indexNumber)
      verExp modifyModule $ EVar indexVar
      return $ EVar $ indexVar
    EInt indexNumber -> do
      let indexVar = Ident $ ident ++ "_" ++ (show indexNumber)
      verExp modifyModule $ EVar indexVar
      return $ EVar $ indexVar

verValExp modifyModule EValue = do
  return EValue

-- czy na pewno tak można?
verValExp modifyModule ESender = do
  mod <- modifyModule id
  let actualSender = whichSender mod
  return $ EVar actualSender

verValExp modifyModule (EInt x) =
  return (EInt x)

-- strings only used as users names
verValExp modifyModule (EStr s) = do
  number <- getPlayerNumber s
  return (EInt number)

verValExp _ ETrue =
  return ETrue

verValExp _ EFalse =
  return EFalse


------------
-- Random --
------------
verRandom :: ModifyModuleType -> Exp -> VerRes Exp
verRandom modifyModule (EInt range) = do
  mod <- modifyModule id
  let localVarName = (moduleName mod) ++ sLocalSuffix ++ (show $ numLocals mod)
  addLocal modifyModule (TUInt range)
  addTransToNewState 
    modifyModule 
    ""
    []
    -- TODO: Alive?
    (foldl
      (\acc x -> acc ++ [([(Ident localVarName, EInt x)], [Alive])])
      []
      [0..(range - 1)]
    )
  return (EVar $ Ident localVarName)

verRandomLazy :: ModifyModuleType -> Exp -> VerRes Exp
verRandomLazy modifyModule (EInt range) = do
  return $ EInt range

-----------------------------
-- Call auxilary functions --
-----------------------------

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
  let retVarIdent = Ident ((unident name) ++ sReturnValueSuffix)
  addReturnVar retVarIdent
  mapM_ (verStm modifyModule) stms
  removeReturnVar
  return (EVar retVarIdent)
--TODO: to jest przepisane z verScFunSendT

-------------
-- ScSendT --
-------------

verSendTAux :: ModifyModuleType -> Ident -> [CallArg] -> VerRes ()
verSendTAux modifyModule funName argsVals = do
  world <- get
  mod <- modifyModule id
  case Map.lookup funName (funs world) of
    Just fun -> do
      let argNames = getArgNames fun
      let expArgsVals = map (\(AExp exp) -> exp) (init argsVals)
      -- TODO: olewamy "from", bo sender jest wiadomy ze scenariusza
      
      let (value, guards1) = case (last argsVals) of (ABra _ value) -> (value, [])
       
      -- TODO: ta linijka chyba jest nie potrzebna w function_without_value
      let updates0 = [[(Ident $ (unident funName) ++ sValueSuffix ++ (show $ number mod), value)]]
      let addAssignment acc (argName, argVal) = acc ++ [createAssignment (number mod) funName argName argVal]
      --TODO: Alive?
      let updates1 = [(foldl addAssignment (head updates0) $ zip argNames expArgsVals, [Alive])]
      

      addTransToNewState 
        modifyModule 
        (sBroadcastPrefix ++ (unident funName) ++ (show $ number mod)) 
        guards1
        updates1

      addTransToNewState
        modifyModule
        ""
        [ 
          EEq 
            (EVar (Ident (unident funName ++ sStatusSuffix ++ (show $ number mod)))) 
            (EVar iTExecuted)
        ]
        --TODO: Alive?
        [([], [Alive])]

-----------
-- SendC --
-----------

verSendCAux :: ModifyModuleType -> Ident -> [Exp] -> VerRes ()
verSendCAux modifyModule funName expArgsVals = do
  world <- get
  mod <- modifyModule id
  case Map.lookup funName (funs world) of
    Just fun -> do
      let argNames = getArgNames fun
      let addAssignment acc (argName, argVal) = acc ++ [createAssignment (number mod) funName argName argVal]
      --TODO: Alive?
      let updates1 = [(foldl addAssignment [] $ zip argNames expArgsVals, [Alive])]
      
      addTransToNewState
        modifyModule
        ""
        []
        updates1

      addTransToNewState
        modifyModule
        (sCommunicatePrefix ++ (unident funName) ++ (show $ number mod))
        []
        --TODO: Alive?
        [([], [Alive])]
    _ -> error $ "Function " ++ (unident funName) ++ " not found in (funs world)"

-- TODO: adds function name in prefix of a variable name
createAssignment :: Integer -> Ident -> Arg -> Exp -> (Ident, Exp)
createAssignment playerNumber funName (Ar _ varName) exp =
  (createScenarioArgumentName funName varName playerNumber, exp)
