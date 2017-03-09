module SmartFunPrismEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import AbsEthver
import AuxPrismEthver
import AuxWorldPrismEthver
import CodePrismEthver
import ConstantsEthver
import WorldPrismEthver

-- for a given function creates a command for every valuation of condVars
createSmartTranss :: ModifyModuleType -> Function -> VerRes ()
createSmartTranss modifyModule (Fun funName args stms) = do
  -- Not needed? vars being added somewhere in higher level
  --mapM_ (\(Ar typ ident) -> addVar modifyModule typ ident) args

  world <- get
  let 
    condVarsList = Set.toList $ condVars world
    condArraysList = arraysAsList $ condArrays world

  case (condVarsList, condArraysList) of
    ([],[]) -> do
      createSmartOneTrans modifyModule (Fun funName args stms) [] [] []
    _ -> do
      types <- typesFromVarsAndArrays condVarsList condArraysList 
      let 
        maxVals = map maxTypeExpOfType types
        valuations = generateAllVals maxVals

      mapM_ (createSmartOneTrans modifyModule (Fun funName args stms) condVarsList condArraysList) valuations

addRandomUpdates :: ModifyModuleType -> [[(Ident, Exp)]] -> VerRes [[(Ident, Exp)]]
addRandomUpdates modifyModule oldUpdates = do
  world <- get
  let
    randomVarsList = Set.toList $ condRandoms world
    randomArraysList = arraysAsList $ condRandomArrays world

  case (randomVarsList, randomArraysList) of
    ([], []) -> return oldUpdates
    _ -> do
      types <- typesFromVarsAndArrays randomVarsList randomArraysList
      
      let
        maxVals = map maxRealValueOfType types
        valuations = generateAllVals maxVals

      randomArraysAsVars <- mapM (arrayToVar modifyModule) randomArraysList
      
      let 
        newUpdates = map
          (\vals -> (zip (randomVarsList ++ randomArraysAsVars) vals) ++ (head oldUpdates))
          valuations

      return newUpdates


-- creates a command for a given function and given valuation
createSmartOneTrans :: ModifyModuleType -> Function -> [Ident] -> [(Ident, Exp)] -> [Exp] -> VerRes ()
-- TODO: FunV
createSmartOneTrans modifyModule (Fun funName args stms) condVarsList condArraysList vals = do
  if (length condVarsList) + (length condArraysList) /= (length vals)
  then
    error $ "|condVarsList| (" ++ (show $ length condVarsList) ++ ") + |condArraysList| (" 
      ++ (show $ length condArraysList) ++ ") /= |vals| (" ++ (show $ length vals) ++ "|)|"
  else
    return ()

  let vals1 = take (length condVarsList) vals
  let vals2 = drop (length condVarsList) vals
  
  addMultipleVarsValues condVarsList vals1

  world <- get
  mod <- modifyModule id
  
  condArraysAsVars <- mapM (arrayToVar modifyModule) condArraysList
  
  addMultipleVarsValues condArraysAsVars vals2

  let 
    guards = map
      (\(varName, val) -> EEq (EVar varName) val)
      (zip (condVarsList ++ condArraysAsVars) vals)
  
  updates <- foldM
    (\acc stm -> do
      newUpdates <- verSmartStm modifyModule stm
      return $ [(head acc) ++ (head newUpdates)]
    )
    [[]]
    stms

  updates <- addRandomUpdates modifyModule updates
 
  world <- get
  let added = addedGuards world

  mod <- modifyModule id

  addCustomTrans
    modifyModule
    ""
    (currState mod)
    1
    (guards ++ added)
    updates

  clearAddedGuards
  clearVarsValues
  clearCondRandoms



---------------------
-- collectCondVars --
---------------------

collectCondVars :: ModifyModuleType -> Stm -> VerRes ()

-- TODO: czy używamy SExp?

collectCondVars modifyModule (SBlock stms) = do
  mapM_ (collectCondVars modifyModule) stms

collectCondVars modifyModule (SAsses asses) = do
  mapM_ (collectCondVarsFromAss modifyModule) asses

collectCondVars modifyModule (SIf cond ifBlock) = do
  collectCondVarsFromExp modifyModule cond
  collectCondVars modifyModule ifBlock

collectCondVars modifyModule (SIfElse cond ifBlock elseBlock) = do
  collectCondVarsFromExp modifyModule cond
  collectCondVars modifyModule ifBlock
  collectCondVars modifyModule elseBlock

-- TODO: Do I really use Return at all?
collectCondVars modifyModule (SReturn _) = do
  return ()

collectCondVars modifyModule (SSend address value) = do
  collectCondVarsFromExp modifyModule address
  collectCondVarsFromExp modifyModule value

----------------------------
-- collectCondVarsFromAss --
----------------------------

collectCondVarsFromAss :: ModifyModuleType -> Ass -> VerRes ()

-- TODO: dorobić: po przypisaniu A := B wpisuje A na liste "overwritten".
-- Potem jak cos z overwritten sie pojawia po prawej, to nie dodawac do cond.
collectCondVarsFromAss modifyModule (AAss ident value) = do
  case value of 
    -- TODO: random dla Booli
    -- TODO: range of random is ignored. Real range deducted from variable type
    (ECall [sRandom] [AExp (EInt range)]) ->
      return ()
    (ECall funs args) ->
      error $ "ECall " ++ (show funs) ++ " (" ++ (show args) ++ ") not supported."
    _ ->
      collectCondVarsFromExp modifyModule value

collectCondVarsFromAss modifyModule (AArrAss ident index value) = do
  case value of
    -- TODO: range of random is ignored. Real range deducted from variable type
    (ECall [sRandom] [AExp (EInt range)]) -> do
      collectCondVarsFromExp modifyModule index
    (ECall funs args) ->
      error $ "ECall " ++ (show funs) ++ " (" ++ (show args) ++ ") not supported."
    _ -> do
      collectCondVarsFromExp modifyModule index
      collectCondVarsFromExp modifyModule value

-- TODO: do wywalenia
{-
collectCondVarsFromRandom :: ModifyModuleType -> Ident -> VerRes ()
collectCondVarsFromRandom modifyModule varName = do
  addCondRandom varName
  
collectCondArraysFromRandom :: ModifyModuleType -> Ident -> Exp -> VerRes ()
collectCondArraysFromRandom modifyModule varName index = 
  addCondRandomArray varName index
-}

-----------------------------
-- collectCondVarsFromExp --
-----------------------------

collectCondVarsFromExp :: ModifyModuleType -> Exp -> VerRes ()
collectCondVarsFromExp modifyModule exp = case exp of
  EOr e1 e2 -> collect2arg modifyModule e1 e2
  EAnd e1 e2 -> collect2arg modifyModule e1 e2
  EEq e1 e2 -> collect2arg modifyModule e1 e2
  ENe e1 e2 -> collect2arg modifyModule e1 e2
  ELt e1 e2 -> collect2arg modifyModule e1 e2
  ELe e1 e2 -> collect2arg modifyModule e1 e2
  EGt e1 e2 -> collect2arg modifyModule e1 e2
  EGe e1 e2 -> collect2arg modifyModule e1 e2
  EAdd e1 e2 -> collect2arg modifyModule e1 e2
  ESub e1 e2 -> collect2arg modifyModule e1 e2
  EMul e1 e2 -> collect2arg modifyModule e1 e2
  EDiv e1 e2 -> collect2arg modifyModule e1 e2
  EMod e1 e2 -> collect2arg modifyModule e1 e2

  ENeg e -> collectCondVarsFromExp modifyModule e
  ENot e -> collectCondVarsFromExp modifyModule e
  
  EArray name index -> do
    collectCondVarsFromExp modifyModule index
    collectCondArray modifyModule name index

  -- TODO: EWait should be moved to Stm
  -- and is not used in contract functions
  -- ECall -> should be moved to Stm
  -- ESend -> should be moved to Stm? (maybe not for checking ret value)
  
  EVar ident -> addCondVar ident

  EValue -> collectCondVarsFromExp modifyModule $ EVar iValue
  ESender -> do
    mod <- modifyModule id
    let actualSender = whichSender mod
    collectCondVarsFromExp modifyModule $ EVar actualSender
  EStr _ -> return ()
  EInt _ -> return ()
  ETrue -> return ()
  EFalse -> return ()

collect2arg :: ModifyModuleType -> Exp -> Exp -> VerRes ()
collect2arg modifyModule e1 e2 = do
  collectCondVarsFromExp modifyModule e1
  collectCondVarsFromExp modifyModule e2

collectCondArray :: ModifyModuleType -> Ident -> Exp -> VerRes ()
collectCondArray modifyModule varName index = do
  addCondArrays varName index

---------------------
-- verSmartStm Aux --
---------------------

-- updatesFromAss ass
updatesFromAss :: ModifyModuleType -> Ass -> VerRes [[(Ident, Exp)]]
updatesFromAss modifyModule (AAss ident exp) = do
  case exp of
    ECall [sRandom] _ -> do
      addCondRandom ident
      return [[]]
    ECall funs args -> error $ "Updates from ECall " ++ (show funs) ++ "(" ++ (show args) ++ ") not supported."
    _ -> do
      val <- evaluateExp modifyModule exp
      return [[(ident, val)]]

updatesFromAss modifyModule (AArrAss (Ident ident) index exp) = do
  case exp of
    -- random calls handled separately in addRandomUpdates
    ECall [sRandom] _ -> do
      addCondRandomArray (Ident ident) index
      return [[]]
    ECall funs args -> error $ "Updates from ECall " ++ (show funs) ++ "(" ++ (show args) ++ ") not supported."
    _ -> do
      indexEIntVal <- case index of
        ESender -> do
          world <- get
          mod <- modifyModule id
          return $ Map.lookup (whichSender mod) (varsValues world)
        EVar varName -> do
          world <- get
          mod <- modifyModule id
          return $ Map.lookup varName (varsValues world)
        -- TODO: EStr
        EInt x -> return $ Just $ EInt x
        _ -> error $ "Array index different than ESender, EInt a, or EVar a"
      let 
        indexVal = case indexEIntVal of
          (Just (EInt x)) -> x
          Nothing -> error $ "Array index: " ++ (show indexEIntVal) ++ "  different than (Just EInt a)"

      updatesFromAss modifyModule $ AAss (Ident $ ident ++ "_" ++ (show indexVal)) exp
     
-----------------
-- verSmartStm --
-----------------

verSmartStm :: ModifyModuleType -> Stm -> VerRes [[(Ident, Exp)]]

-- TODO: SExp - czy to na pewno jest niepotrzebne?
verSmartStm modifyModule (SExp exp) = do
  return [[]]

verSmartStm modifyModule (SBlock stms) = do
  -- TODO: inteligentne powiększanie updateów w przypadku probabilistycznych przejsc
  foldM
    (\acc stm -> do
      newUpdates <- verSmartStm modifyModule stm
      -- TODO: assumption that newUpdates is a signleton (no probability)
      -- TODO: Czy to nie problem, że jest return w pętli? (czy sie nie przerwie po pierwszym obrocie?)
      return $ [(head acc) ++ (head newUpdates)]
    )
    [[]]
    stms

verSmartStm modifyModule (SAsses asses) = do
  -- TODO: inteligentne powiększanie updateów przy probabilistycznych przejsciach
  
  foldM
    (\acc ass -> do
      newUpdates <- updatesFromAss modifyModule ass
      -- TODO: assumption that newUpdates is a singleton (no probability)
      mapM_ (\(ident, val) -> assignVarValue ident val) (head newUpdates)
      -- TODO: assumption that newUpdates is a singleton (no probability)
      return $ [(head acc) ++ (head newUpdates)]
    )
    [[]]
    asses

verSmartStm modifyModule (SIf cond stm) = do
  result <- evaluateExp modifyModule cond
  case result of
    ETrue -> verSmartStm modifyModule stm
    EFalse -> return [[]]
    _ -> error $ "Error in verSmartStm(SIf): condition not evaluated to bool: " ++ (show result)

verSmartStm modifyModule (SIfElse cond stm1 stm2) = do
  result <- evaluateExp modifyModule cond
  case result of
    ETrue -> verSmartStm modifyModule stm1
    EFalse -> verSmartStm modifyModule stm2
    _ -> error $ "Error in verSmartStm(SIf): condition not evaluated to bool: " ++ (show result)

verSmartStm modifyModule (SReturn exp) = do
  error $ "SReturn usage not supported"

verSmartStm modifyModule (SSend receiverExp arg) = do
  val <- evaluateExp modifyModule arg
  mod <- modifyModule id
  let actualSender = whichSender mod
  case receiverExp of
    ESender -> do
      verSmartStm
        modifyModule
        (SIf
          (EEq (EVar actualSender) (EInt 0))
          (SSend (EInt 0) arg)
        )
      verSmartStm
        modifyModule
        (SIf
          (EEq (EVar actualSender) (EInt 1))
          (SSend (EInt 1) arg)
        )
    EStr receiverAddress -> do
      receiverNumber <- getPlayerNumber receiverAddress
      let receiverBalance = Ident $ sBalancePrefix ++ (show receiverNumber)
      smartTransferFromContract receiverBalance val
    EInt receiverNumber -> do
      let receiverBalance = Ident $ sBalancePrefix ++ (show receiverNumber)
      smartTransferFromContract receiverBalance val


------------------
-- evaluateExp --
------------------

evaluateBoolBinOp :: ModifyModuleType -> (Bool -> Bool -> Bool) -> Exp -> Exp -> VerRes Exp
evaluateBoolBinOp modifyModule op e1 e2 = do
  v1 <- evaluateExp modifyModule e1
  v2 <- evaluateExp modifyModule e2
  let bool1 = case v1 of
        ETrue -> True
        EFalse -> False
        _ -> error $ "Error in evaluateBoolBinOp: not a bool value: " ++ (show v1)
  let bool2 = case v2 of
        ETrue -> True
        EFalse -> False
        _ -> error $ "Error in evaluateBoolBinOp: not a bool value: " ++ (show v2)
  
  return $ expFromBool $ op bool1 bool2

evaluateArithmIntBinOp :: ModifyModuleType -> (Integer -> Integer -> Integer) -> Exp -> Exp -> VerRes Exp
evaluateArithmIntBinOp modifyModule op e1 e2 = do
  v1 <- evaluateExp modifyModule e1
  v2 <- evaluateExp modifyModule e2
  case intFromExp v1 of 
    Nothing -> error $ "Error in evaluateArithmIntBinOp: not an Int value: " ++ (show v1)
    Just x1 -> case intFromExp v2 of
      Nothing -> error $ "Error in evaluateArithmIntBinOp: not an Int value: " ++ (show v2)
      Just x2 -> return $ expFromInt $ op x1 x2

evaluateCompIntBinOp :: ModifyModuleType -> (Integer -> Integer -> Bool) -> Exp -> Exp -> VerRes Exp
evaluateCompIntBinOp modifyModule op e1 e2 = do
  v1 <- evaluateExp modifyModule e1
  v2 <- evaluateExp modifyModule e2
  case intFromExp v1 of 
    Nothing -> error $ "Error in evaluateCompIntBinOp: not an Int value: " ++ (show v1)
    Just x1 -> case intFromExp v2 of
      Nothing -> error $ "Error in evaluateCompIntBinOp: not an Int value: " ++ (show v2)
      Just x2 -> return $ expFromBool $ op x1 x2

evaluateEq :: ModifyModuleType -> Exp -> Exp -> VerRes Exp
evaluateEq modifyModule e1 e2 = do
  world <- get
  v1 <- evaluateExp modifyModule e1
  v2 <- evaluateExp modifyModule e2
  t1 <- findType v1
  t2 <- findType v2
  case (t1, t2) of 
    (Just TBool, Just TBool) -> return $ expFromBool $ v1 == v2
    (Just (TUInt _), Just (TUInt _)) -> do
      return $ expFromBool $ v1 == v2
    _ -> error $ "Error in evaluateBoolIntBinOp: not matching types: " ++ (show v1) ++ " and " ++ (show v2)

evaluateBoolUnOp :: ModifyModuleType -> (Bool -> Bool) -> Exp -> VerRes Exp
evaluateBoolUnOp modifyModule op e = do
  v <- evaluateExp modifyModule e
  let bool = case v of
        ETrue -> True
        EFalse -> False
        _ -> error $ "Error in evaluateBoolUnOp: not a bool value: " ++ (show v)

  return $ expFromBool $ op bool

-- evaluateExp

evaluateExp :: ModifyModuleType -> Exp -> VerRes Exp

evaluateExp modifyModule (EOr e1 e2) = evaluateBoolBinOp modifyModule (||) e1 e2
evaluateExp modifyModule (EAnd e1 e2) = evaluateBoolBinOp modifyModule (&&) e1 e2

evaluateExp modifyModule (EEq e1 e2) = evaluateEq modifyModule e1 e2
evaluateExp modifyModule (ENe e1 e2) = do
  tmp <- evaluateEq modifyModule e1 e2
  evaluateBoolUnOp modifyModule not tmp

evaluateExp modifyModule (ELt e1 e2) = evaluateCompIntBinOp modifyModule (<) e1 e2
evaluateExp modifyModule (ELe e1 e2) = evaluateCompIntBinOp modifyModule (<=) e1 e2
evaluateExp modifyModule (EGt e1 e2) = evaluateCompIntBinOp modifyModule (>) e1 e2
evaluateExp modifyModule (EGe e1 e2) = evaluateCompIntBinOp modifyModule (>=) e1 e2
evaluateExp modifyModule (EAdd e1 e2) = evaluateArithmIntBinOp modifyModule (+) e1 e2
evaluateExp modifyModule (ESub e1 e2) = evaluateArithmIntBinOp modifyModule (-) e1 e2
evaluateExp modifyModule (EMul e1 e2) = evaluateArithmIntBinOp modifyModule (*) e1 e2
evaluateExp modifyModule (EDiv e1 e2) = evaluateArithmIntBinOp modifyModule div e1 e2
evaluateExp modifyModule (EMod e1 e2) = evaluateArithmIntBinOp modifyModule mod e1 e2

evaluateExp modifyModule (ENeg e) = evaluateArithmIntBinOp modifyModule (-) (EInt 0) e
evaluateExp modifyModule (ENot e) = evaluateBoolUnOp modifyModule not e

evaluateExp modifyModule (EArray (Ident ident) index) = do
  mod <- modifyModule id
  indexEvaluated <- evaluateExp modifyModule index
  case indexEvaluated of 
    EInt indexVal -> evaluateExp modifyModule $ EVar $ Ident $ ident ++ "_" ++ (show indexVal)
    _ -> error $ "Index " ++ (show indexEvaluated) ++ " doesn't evaluate to EInt a)"

-- TODO: should be moved to SWait?
--evaluateExp modifyModule (EWait ...)

evaluateExp modifyModule (EVar ident) = do
  exp <- findVarValue ident
  case exp of 
    Just val -> return val
    Nothing -> return $ EVar ident

evaluateExp modifyModule (EValue) = do
  evaluateExp modifyModule (EVar $ Ident sValue)

-- TODO: zrobić coś z senderem. Pewnie trzeba dodać do condVars i trzymać wartość w varsValues
evaluateExp modifyModule ESender = do
  world <- get
  mod <- modifyModule id
  case Map.lookup (whichSender mod) (varsValues world) of
    Just x -> return x
    Nothing -> error $ "Variable " ++ (show $ whichSender mod) ++ " not found in varsValues."

evaluateExp modifyModule (EStr name) = do
  world <- get
  case Map.lookup name $ playerNumbers world of
    Nothing -> error $ "Player '" ++ name ++ "' not found. (other string constants not supported)"
    Just number -> return (EInt number)

evaluateExp modifyModule (EInt x) = do
  return (EInt x)

evaluateExp modifyModule ETrue = do
  return ETrue

evaluateExp modifyModule EFalse = do
  return EFalse
