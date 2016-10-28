module ExpPrismEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map

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
verStm modifyModule (SExp exp) = do
  _ <- verExp modifyModule exp 
  return ()

verStm modifyModule (SAsses [AAss ident exp]) = 
  verFullAss modifyModule (AAss ident exp)

verStm modifyModule (SAsses [AArrAss ident index exp]) =
  verFullAss modifyModule (AArrAss ident index exp)

verStm modifyModule (SAsses asses) = do
  assignments <- mapM (generateSimpleAss modifyModule) asses
  let (unzippedGuards, unzippedUpdates) = unzip assignments
  let (guards, updates) = (concat unzippedGuards, concat unzippedUpdates)

  addTransToNewState
    modifyModule
    ""
    guards
    [updates]
  

verStm modifyModule (SReturn exp) = do
  evalExp <- verExp modifyModule exp 
  world <- get 
  verStm modifyModule (SAsses [AAss (head $ returnVar world) evalExp])

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

---------
-- Ass --
---------

verFullAss :: ModifyModuleType -> Ass -> VerRes ()

verFullAss modifyModule (AAss ident exp) = do
  (guards, updates) <- generateSimpleAss modifyModule (AAss ident exp)
      
  addTransToNewState
    modifyModule
    ""
    guards
    [updates]

verFullAss modifyModule (AArrAss (Ident ident) index exp) = do
  case index of
    ESender -> do
      mod <- modifyModule id
      let actualSender = whichSender mod
      verStm 
        modifyModule 
        (SIf 
          (EEq (EVar actualSender) (EInt 0))
          (SAsses [AAss (Ident $ ident ++ "_0") exp])
        )
      verStm
        modifyModule
        (SIf
          (EEq (EVar actualSender) (EInt 1))
          (SAsses [AAss (Ident $ ident ++ "_1") exp])
        )
    EVar v -> do
      var <- verExp modifyModule (EVar v)
      verStm 
        modifyModule 
        (SIf 
          (EEq var (EInt 0))
          (SAsses [AAss (Ident $ ident ++ "_0") exp])
        )
      verStm
        modifyModule
        (SIf
          (EEq var (EInt 1))
          (SAsses [AAss (Ident $ ident ++ "_1") exp])
        )
    EStr indexAddress -> do
      indexNumber <- getPlayerNumber indexAddress
      let indexVar = Ident $ ident ++ "_" ++ (show indexNumber)
      verStm modifyModule $ SAsses [AAss indexVar exp]
    EInt indexNumber -> do
      let indexVar = Ident $ ident ++ "_" ++ (show indexNumber)
      verStm modifyModule $ SAsses [AAss indexVar exp]

-- generateSimpleAss

-- returns simple updates [], not [[]]
generateSimpleAss :: ModifyModuleType -> Ass -> VerRes ([Exp], [(Ident, Exp)])
generateSimpleAss modifyModule (AAss ident exp) = do
  evalExp <- verExp modifyModule exp 
  typ <- findVarType ident
  minV <- minValue ident
  maxV <- maxTypeValue ident
  let guards = case typ of Just TBool -> []
                           Just _ -> [EGe evalExp (EInt minV), ELe evalExp (EInt maxV)]
  return (guards, [(ident, evalExp)])

generateSimpleAss modifyModule (AArrAss (Ident ident) index exp) = do
  case index of
    -- TODO: ESender (zmienić też verFullAss)
    EStr indexAddress -> do
      indexNumber <- getPlayerNumber indexAddress
      let indexVar = Ident $ ident ++ "_" ++ (show indexNumber)
      generateSimpleAss modifyModule $ AAss indexVar exp 
    EInt indexNumber -> do
      let indexVar = Ident $ ident ++ "_" ++ (show indexNumber)
      generateSimpleAss modifyModule $ AAss indexVar exp 


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

verExp modifyModule (ECall idents exps) = verCallExp modifyModule (ECall idents exps)
verExp modifyModule (ESend receiver args) = verCallExp modifyModule (ESend receiver args)
verExp modifyModule (EWait cond) = verCallExp modifyModule (EWait cond)

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
  case Map.lookup ident $ argMap world of
    Just varName -> return (EVar varName)
    Nothing -> return (EVar ident)

verValExp modifyModule (EArray (Ident ident) index) = do
  mod <- modifyModule id
  let localVarName = (moduleName mod) ++ sLocalSufix ++ (show $ numLocals mod)
  -- TODO: liczba graczy = 2
  maybeType <- findVarType $ Ident $ ident ++ "_0"
  
  case index of
    ESender -> do
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
    EVar v -> do
      case maybeType of
        Just typ -> do
          addLocal modifyModule typ
          var <- verExp modifyModule (EVar v)
          verStm 
            modifyModule 
            (SIf 
              (EEq var (EInt 0))
              (SAsses [AAss (Ident $ localVarName) (EVar $ Ident $ ident ++ "_0")])
            )
          verStm
            modifyModule
            (SIf
              (EEq var (EInt 1))
              (SAsses [AAss (Ident $ localVarName) (EVar $ Ident $ ident ++ "_1")])
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

verValExp modifyModule (EStr s) = do
  number <- getPlayerNumber s
  return (EInt number)

verValExp _ ETrue =
  return ETrue

verValExp _ EFalse =
  return EFalse


----------------
-- CallExp --
----------------

-- TODO: na razie możemy mieć tylko jeden kontrakt
verCallExp :: ModifyModuleType -> Exp -> VerRes Exp

verCallExp modifyModule (ECall idents args) = do
  case idents of
    [funName, sufix] 
      | sufix == iSendTransaction -> do 
        verSendTAux modifyModule funName args
        return (ECall idents args)
      | sufix == iSendCommunication -> do
        verSendCAux modifyModule funName args
        return (ECall idents args)
      | sufix == iCall -> do
        verCallAux modifyModule funName args
    [ident]
      | ident == iRandom -> do
        verRandom modifyModule args
      | ident == iRandomLazy -> do
        verRandomLazy modifyModule args


verCallExp modifyModule (ESend receiverExp args) = do
  case args of
    [AExp arg] -> do
      val <- verExp modifyModule arg
      mod <- modifyModule id
      let actualSender = whichSender mod
      case receiverExp of
        ESender -> do
          verStm 
            modifyModule 
            (SIf 
              (EEq (EVar actualSender) (EInt 0))
              (SExp $ ESend (EInt 0) args)
            )
          verStm
            modifyModule
            (SIf
              (EEq (EVar actualSender) (EInt 1))
              (SExp $ ESend (EInt 1) args)
            )
        EStr receiverAddress -> do
          receiverNumber <- getPlayerNumber receiverAddress
          let receiverBalance = Ident $ sBalancePrefix ++ (show receiverNumber) 
          transferFromContract receiverBalance val
        EInt receiverNumber -> do
          let receiverBalance = Ident $ sBalancePrefix ++ (show receiverNumber)
          transferFromContract receiverBalance val
  return (ESend receiverExp args)

verCallExp modifyModule (EWait cond) = do
  evalCond <- verExp modifyModule cond
  addTransToNewState
    modifyModule
    ""
    [EOr evalCond $ EVar $ Ident sTimelocksReleased]
    [[]]
  return (EWait evalCond)

------------
-- Random --
------------

verRandom :: ModifyModuleType -> [CallArg] -> VerRes Exp
verRandom modifyModule [AExp (EInt range)] = do
  mod <- modifyModule id
  let localVarName = (moduleName mod) ++ sLocalSufix ++ (show $ numLocals mod)
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

verRandomLazy :: ModifyModuleType -> [CallArg] -> VerRes Exp
verRandomLazy modifyModule [AExp (EInt range)] = do
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
  let retVarIdent = Ident ((unident name) ++ sReturnValueSufix)
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
      let updates0 = [[(Ident $ (unident funName) ++ sValueSufix ++ (show $ number mod), value)]]
      let addAssignment acc (argName, argVal) = acc ++ [createAssignment (number mod) funName argName argVal]
      let updates1 = [foldl addAssignment (head updates0) $ zip argNames expArgsVals]
      

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
            (EVar (Ident (unident funName ++ sStatusSufix ++ (show $ number mod)))) 
            (EVar iTExecuted)
        ]
        [[]]

-----------
-- SendC --
-----------

verSendCAux :: ModifyModuleType -> Ident -> [CallArg] -> VerRes ()
verSendCAux modifyModule funName argsVals = do
  world <- get
  mod <- modifyModule id
  case Map.lookup funName (funs world) of
    Just fun -> do
      let argNames = getArgNames fun
      let expArgsVals = map (\(AExp exp) -> exp) argsVals
      -- TODO: olewamy "from", bo sender jest wiadomy ze scenariusza
      let addAssignment acc (argName, argVal) = acc ++ [createAssignment (number mod) funName argName argVal]
      let updates1 = [foldl addAssignment [] $ zip argNames expArgsVals]
      
      addTransToNewState
        modifyModule
        ""
        []
        updates1

      addTransToNewState
        modifyModule
        (sCommunicatePrefix ++ (unident funName) ++ (show $ number mod))
        []
        [[]]

createAssignment :: Integer -> Ident -> Arg -> Exp -> (Ident, Exp)
createAssignment playerNumber funName (Ar _ (Ident varName)) exp =
  (Ident $ unident funName ++ "_" ++ varName ++ (show playerNumber), exp)
