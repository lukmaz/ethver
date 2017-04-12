module DFSPrismEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import AbsEthver
import AuxPrismEthver
import AuxWorldPrismEthver
import CodePrismEthver
import ConstantsEthver
import WorldPrismEthver

---------------
-- verDFSFun --
---------------

-- for a given function creates a command for every important valuation
verDFSFun :: ModifyModuleType -> Function -> VerRes ()
verDFSFun modifyModule (Fun funName args stms) = do
  mod <- modifyModule id
  let
    stVar = Ident $ stateVar mod
    initGuards = [EEq (EVar stVar) (EInt $ currState mod)]
    initUpdates = [[(stVar, EInt 1)]]
  trs <- verDFSStm modifyModule (SBlock stms) [("", initGuards, initUpdates)]
  mapM_
    (\tr -> modifyModule (\mod -> mod {transs = tr:(transs mod)}))
    trs

---------------
-- verDFSStm --
---------------

-- TODO: zmienić na appplyToTrList
-- interprets stm and applies result to every tr in trs
verDFSStm :: ModifyModuleType -> Stm -> [Trans] -> VerRes ([Trans])

verDFSStm modifyModule stm trs = do
  foldM
    (\acc tr -> do
      newTrs <- addDFSStm modifyModule stm tr
      return $ acc ++ newTrs
    )
    []
    trs

---------------
-- addDFSStm --
---------------

-- interprets stm and applies result to a particular tr
addDFSStm :: ModifyModuleType -> Stm -> Trans -> VerRes ([Trans])

addDFSStm modifyModule (SBlock []) tr = do
  return [tr]

addDFSStm modifyModule (SBlock (stmH:stmT)) tr = do
  newTrs <- addDFSStm modifyModule stmH tr
  verDFSStm modifyModule (SBlock stmT) newTrs

addDFSStm modifyModule (SAss ident exp) tr = do
  applyFunToStmWithEvaluation modifyModule addAssToTr (SAss ident exp) tr

addDFSStm modifyModule (SArrAss ident index exp) tr = do
  applyFunToStmWithEvaluation modifyModule addAssToTr (SArrAss ident index exp) tr
  
addDFSStm modifyModule (SIf cond ifBlock) tr = do
  let oldTr = tr

  (condTranss, _) <- evaluateExp modifyModule cond oldTr
  posTranss <- applyToTrList modifyModule (addDFSStm modifyModule ifBlock) condTranss

  (negCondTranss, _) <- evaluateExp modifyModule (negateExp cond) oldTr
  
  return $ posTranss ++ negCondTranss

addDFSStm modifyModule (SIfElse cond ifBlock elseBlock) tr = do
  let oldTr = tr
  (condTranss, _) <- evaluateExp modifyModule cond oldTr
  posTranss <- applyToTrList modifyModule (addDFSStm modifyModule ifBlock) condTranss

  (negCondTranss, _) <- evaluateExp modifyModule (negateExp cond) oldTr
  negTranss <- applyToTrList modifyModule (addDFSStm modifyModule elseBlock) negCondTranss
  
  return $ posTranss ++ negTranss

addDFSStm modifyModule (SWhile _ _) _ = do
  error $ "while loop not supported in verDFS"

-------------------------------------------------
-- applyFun with evaluation ---------------------
-- evaluates the argument and applies function --
-------------------------------------------------

-- ZWRACANIE STM DO WYWALENIA
-- TODO: może też zrezygnować ze zwracania Stm?


---------------------------
-- WAZNE TODO
---------------------------

-------------------
-- applyToTrList --
-------------------

-- TODO: może zostawić tylko tę funkcję i reszta niech z niej korzysta?
applyToTrList :: ModifyModuleType -> (Trans -> VerRes [Trans]) -> [Trans] -> VerRes [Trans]
applyToTrList modifyModule fun trs = do
  foldM
    (\acc tr -> do
      newTrs <- fun tr
      return $ acc ++ newTrs
    )
    []
    trs

-- TODO: zamienić kolejność argumentów funkcji, żeby Trans było na końcu
-- Żeby się dało skorzystać z applyToTrList

applyFunToStmWithEvaluation :: ModifyModuleType -> (Stm -> Trans -> VerRes [Trans]) -> Stm -> Trans -> VerRes [Trans]
applyFunToStmWithEvaluation modifyModule fun stm tr = do
  (trs, _) <- evaluateStm modifyModule stm tr
  foldM
    (\acc tr -> do
      newTrs <- fun (determineStm stm tr) tr
      return $ acc ++ newTrs
    )
    []
    trs


---------
-- Aux --
---------

-- cheks if a cond is of the only supported type 
-- checkCond
-- TODO



-- special case for SAss. Generates single trans
addVarAssToTr :: Stm -> Trans -> VerRes Trans

addVarAssToTr (SAss varName exp) (trName, guards, updates) = do
  newUpdates <- foldM
    (\acc branch -> do
      partialUpdates <- addAssToUpdatesBranch guards (SAss varName exp) branch
      return $ partialUpdates ++ acc
    )
    []
    updates
  return $ (trName, guards, newUpdates)

addVarAssToTr (SArrAss arrName index exp) _ = do
  error $ "addVarAssToTr should not be called with SArrAss argument (" ++ (show (SArrAss arrName index exp))

-- adds an assignment to a single transition
-- can possibly create longer list of updates in case the array index is not known
addAssToTr :: Stm -> Trans -> VerRes [Trans]

addAssToTr (SAss varName exp) tr = do
  newTr <- addVarAssToTr (SAss varName exp) tr
  return [newTr]


-- TODO DFS: to jest do przeniesienia do evaluateExp?
addAssToTr (SArrAss (Ident arrName) index exp) (trName, guards, updates) = do
  case index of
    {-
    ESender -> do -- TODO: np. trzeba dodać sendera do varsValues
      world <- get
      mod <- modifyModule id
      return $ Map.lookup (whichSender mod) (varsValues world)
    -}
    EInt x -> do
      addAssToTr (SAss (Ident $ arrName ++ "_" ++ (show x)) exp) (trName, guards, updates)
    EVar varName -> do 
      case deduceVarValueFromGuards guards varName of
        (Just (EInt x)) -> do
          addAssToTr (SAss (Ident $ arrName ++ "_" ++ (show x)) exp) (trName, guards, updates)
        Nothing -> do
          varType <- findVarType varName 
          case varType of
            Just typ -> do
              let 
                maxVal = maxTypeValueOfType typ
                vals = [0..maxVal]
              mapM
                (\val -> 
                  addVarAssToTr 
                    (SAss (Ident $ arrName ++ "_" ++ (show val)) exp)
                    (trName, (EEq (EVar varName) (EInt val)):guards, updates) 
                )
                vals
            Nothing -> 
              error $ "Var " ++ (unident varName) ++ " not found by findVarType"
    _ -> do
      error $ "Array index different than ESender, EInt a, or EVar a"


-- modifyModule niepotrzebne?
-- TODO: only simple assignments for a moment
-- TODO: random
-- Aux: adds an assignment to an updates branch
-- can possibly create longer list of updates for randomized assignment
addAssToUpdatesBranch :: [Exp] -> Stm -> [(Ident, Exp)] -> VerRes [[(Ident, Exp)]]

addAssToUpdatesBranch guards (SAss ident exp) updatesBranch = do
  -- TODO random (może przepisać case exp z updatesFromAss z SmartFunPrismEthver.hs?
  let 
    deleteOld :: [(Ident, Exp)] -> [(Ident, Exp)]
    deleteOld list = filter
      (\(i, _) -> i /= ident)
      list
    newUpdates =  
      (((ident, exp):) . deleteOld)
      updatesBranch
  return [newUpdates]

addAssToUpdatesBranch _  (SArrAss arrName index exp) _ = do
  error $ "addAssToUpdateBranch should not be called with SArrAss (" ++ (show $ SArrAss arrName index exp)
  

deduceVarValueFromGuards :: [Exp] -> Ident -> Maybe Exp
deduceVarValueFromGuards guards varName = 
  let
    filteredGuards =
      filter
      (\x -> case x of
        Just _ -> True
        _ -> False
      )
      (map (valueFromCond varName) guards)
  in
    case filteredGuards of
      (h:t) -> h
      _ -> Nothing

valueFromCond :: Ident -> Exp -> Maybe Exp
valueFromCond varName cond = 
  case cond of
    (EEq (EVar someVar) val) -> 
      if someVar == varName
        then Just val
        else Nothing
    (EAnd c1 c2) ->
      case ((valueFromCond varName c1), (valueFromCond varName c2)) of
        (Just val, _) -> Just val
        (_, Just val) -> Just val
        _ -> Nothing
    _ -> Nothing

-- TODO: Czy musi być deduceVarValueFromUpdate?

-- Aux: deduces value of a var from guards and updates
{-
deduceVarValue :: [Exp] -> [(Ident, Exp)] -> Ident -> Maybe Exp
deduceVarValue guards updatesBranch varName =
  -- TODO: nested guards
  let
    filteredGuards = 
      filter
      (\x -> case x of
        Just _ -> True
        _ -> False
      )
      (map (valueFromCond varName) guards)
    filteredUpdates = filter (\(i, e) -> i == varName) updatesBranch
  in
    case filteredUpdates of
      (h:t) -> Just h
      _ -> case filteredGuards of
        (h:t) -> Just h
        _ -> Nothing
-}

--  (createSmartOneTrans modifyModule (Fun funName args stms) condVarsList condArraysList) valuations

{-
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
-}




------------------
-- determineStm --
------------------

-- determines values (e.g. array index) from guards


determineStm :: Stm -> Trans -> Stm

determineStm (SAss ident exp) tr = 
  SAss ident (determineExp exp tr)

determineStm (SArrAss ident index exp) tr = 
  SArrAss ident (determineExp index tr) (determineExp exp tr)

------------------
-- determineExp --
------------------

-- used mainly for EArray: showExp(tab[x]) = tab_2 for x = 2
-- uses x value from guards

determineExp :: Exp -> Trans -> Exp
determineExp (EArray (Ident arrName) index) (trName, guards, updates) = 
  case index of
    EInt x ->
      EVar $ Ident $ arrName ++ "_" ++ (show x)
    EVar varName -> do 
      case deduceVarValueFromGuards guards varName of
        (Just (EInt x)) ->
          EVar $ Ident $ arrName ++ "_" ++ (show x)
        Nothing -> 
          error $ "Array index should be determined when using showExp: " ++ (show $ EArray (Ident arrName) index)
    _ -> 
      error $ "Array index different than ESender, EInt a, or EVar a"

determineExp (EInt x) _ = EInt x

determineExp (EVar varIdent) (trName, guards, updates) = 
  case deduceVarValueFromGuards guards varIdent of
    (Just (EInt x)) ->
      EInt x
    Nothing ->
      EVar varIdent
      -- chyba musi tak być, bo jak inaczej sobie poradzić z wartością argumentu funkcji?
      --error $ "Value of variable " ++ (show varIdent) ++ " not determined from guards: " ++ (show guards)


-----------------
-- evaluateStm --
-----------------

evaluateStm :: ModifyModuleType -> Stm -> Trans -> VerRes ([Trans], Stm)

evaluateStm modifyModule (SAss ident exp) tr = do
  (trs, evaluatedExp) <- evaluateExp modifyModule exp tr
  return (trs, SAss ident evaluatedExp)

evaluateStm modifyModule (SArrAss ident index exp) tr = do
  trs <- evaluate2Exp modifyModule index exp tr
  return (trs, SArrAss ident index exp)

evaluate2Exp :: ModifyModuleType -> Exp -> Exp -> Trans -> VerRes [Trans]
evaluate2Exp modifyModule exp1 exp2 tr = do
  (trs, _) <- evaluateExp modifyModule exp1 tr
  foldM
    (\acc tr -> do
      -- TODO: nie ma jak wyciągnąć jednego evaluatedExp2, bo jest pętla
      (newTrs, _) <- evaluateExp modifyModule exp2 tr
      return $ acc ++ newTrs
    )
    []
    trs

-----------------
-- evaluateExp --
-----------------

evaluateExp :: ModifyModuleType -> Exp -> Trans -> VerRes ([Trans], Exp)
{-
evaluateExp modifyModule (EOr e1 e2) = evaluateBoolBinOp modifyModule (||) e1 e2 tr
evaluateExp modifyModule (EAnd e1 e2) = evaluateBoolBinOp modifyModule (&&) e1 e2 tr

evaluateExp modifyModule (EEq e1 e2) = evaluateEq modifyModule e1 e2 tr
evaluateExp modifyModule (ENe e1 e2) = do
  tmp <- evaluateEq modifyModule e1 e2 tr
  evaluateBoolUnOp modifyModule not tmp tr

evaluateExp modifyModule (ELt e1 e2) tr = evaluateCompIntBinOp modifyModule (<) e1 e2 tr
evaluateExp modifyModule (ELe e1 e2) tr = evaluateCompIntBinOp modifyModule (<=) e1 e2 tr
evaluateExp modifyModule (EGt e1 e2) tr = evaluateCompIntBinOp modifyModule (>) e1 e2 tr
evaluateExp modifyModule (EGe e1 e2) tr = evaluateCompIntBinOp modifyModule (>=) e1 e2 tr
evaluateExp modifyModule (EAdd e1 e2) tr = evaluateArithmIntBinOp modifyModule (+) e1 e2 tr
evaluateExp modifyModule (ESub e1 e2) tr = evaluateArithmIntBinOp modifyModule (-) e1 e2 tr
evaluateExp modifyModule (EMul e1 e2) tr = evaluateArithmIntBinOp modifyModule (*) e1 e2 tr
evaluateExp modifyModule (EDiv e1 e2) tr = evaluateArithmIntBinOp modifyModule div e1 e2 tr
evaluateExp modifyModule (EMod e1 e2) tr = evaluateArithmIntBinOp modifyModule mod e1 e2 tr

evaluateExp modifyModule (ENeg e) tr = evaluateArithmIntBinOp modifyModule (-) (EInt 0) e tr
evaluateExp modifyModule (ENot e) tr = evaluateBoolUnOp modifyModule not e tr
-}


--DO WYWALENIA?
{-
evaluateExp modifyModule (EArray (Ident ident) index) tr = do
  mod <- modifyModule id
  
  case index of
  
  
  indexEvaluated <- evaluateExp modifyModule index tr
  case indexEvaluated of 
    EInt indexVal -> evaluateExp modifyModule $ EVar $ Ident $ ident ++ "_" ++ (show indexVal)
    _ -> error $ "Index " ++ (show indexEvaluated) ++ " doesn't evaluate to EInt a)"
-}

evaluateExp modifyModule (EArray (Ident arrName) index) (trName, guards, updates) = do
  case index of
    {-
    JAKIES STARE:
    ESender -> do -- TODO: np. trzeba dodać sendera do varsValues
      world <- get
      mod <- modifyModule id
      return $ Map.lookup (whichSender mod) (varsValues world)
    -}
    EInt x -> do
      return ([(trName, guards, updates)], EVar (Ident $ arrName ++ "_" ++ (show x)))
    EVar varName -> do 
      case deduceVarValueFromGuards guards varName of
        (Just (EInt x)) -> do
          return ([(trName, guards, updates)], EVar (Ident $ arrName ++ "_" ++ (show x)))
        Nothing -> do
          varType <- findVarType varName
          case varType of
            Just typ -> do
              let 
                maxVal = maxTypeValueOfType typ
                vals = [0..maxVal]
                trs = map
                  (\val -> 
                    (trName, (EEq (EVar varName) (EInt val)):guards, updates) 
                  )
                  vals
              -- TODO: Zwraca starą postać. Ale co ma zwracać, skoro wygenerowała kilka?
              -- Może w ogóle evaluateExp nie powinno nic zwracać?
              return (trs, EArray (Ident arrName) index)
            Nothing -> 
              error $ "Var " ++ (unident varName) ++ " not found by findVarType"
    _ -> do
      error $ "Array index different than ESender, EInt a, or EVar a"


evaluateExp modifyModule (EVar ident) tr = do
  exp <- findVarValue ident
  case exp of 
    Just val -> return ([tr], val)
    Nothing -> return ([tr], EVar ident)

evaluateExp modifyModule (EValue) tr = do
  evaluateExp modifyModule (EVar $ Ident sValue) tr

-- TODO DFS: możliwe, że tu trzeba będzie sprawdzać, czy nie dołożyć sendera do guardsów. albo dodawać zawsze domyślnie
evaluateExp modifyModule ESender tr = do
  world <- get
  mod <- modifyModule id
  case Map.lookup (whichSender mod) (varsValues world) of
    Just x -> return ([tr], x)
    Nothing -> error $ "Variable " ++ (show $ whichSender mod) ++ " not found in varsValues."

evaluateExp modifyModule (EStr name) tr = do
  world <- get
  case Map.lookup name $ playerNumbers world of
    Nothing -> error $ "Player '" ++ name ++ "' not found. (other string constants not supported)"
    Just number -> return ([tr], EInt number)

evaluateExp modifyModule (EInt x) tr = do
  return ([tr], EInt x)

evaluateExp modifyModule ETrue tr = do
  return ([tr], ETrue)

evaluateExp modifyModule EFalse tr = do
  return ([tr], EFalse)


---------------------
-- evaluateExp aux --
---------------------

{-
evaluateBoolBinOp :: ModifyModuleType -> Trans -> (Bool -> Bool -> Bool) -> Exp -> Exp -> VerRes ([Trans], Exp)
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

evaluateArithmIntBinOp :: ModifyModuleType -> Trans -> (Integer -> Integer -> Integer) -> Exp -> Exp -> VerRes ([Trans], Exp)
evaluateArithmIntBinOp modifyModule op e1 e2 = do
  v1 <- evaluateExp modifyModule e1
  v2 <- evaluateExp modifyModule e2
  case intFromExp v1 of 
    Nothing -> error $ "Error in evaluateArithmIntBinOp: not an Int value: " ++ (show v1)
    Just x1 -> case intFromExp v2 of
      Nothing -> error $ "Error in evaluateArithmIntBinOp: not an Int value: " ++ (show v2)
      Just x2 -> return $ expFromInt $ op x1 x2

evaluateCompIntBinOp :: ModifyModuleType -> Trans -> (Integer -> Integer -> Bool) -> Exp -> Exp -> VerRes ([Trans], Exp)
evaluateCompIntBinOp modifyModule op e1 e2 = do
  v1 <- evaluateExp modifyModule e1
  v2 <- evaluateExp modifyModule e2
  case intFromExp v1 of 
    Nothing -> error $ "Error in evaluateCompIntBinOp: not an Int value: " ++ (show v1)
    Just x1 -> case intFromExp v2 of
      Nothing -> error $ "Error in evaluateCompIntBinOp: not an Int value: " ++ (show v2)
      Just x2 -> return $ expFromBool $ op x1 x2

evaluateEq :: ModifyModuleType -> Trans -> Exp -> Exp -> VerRes ([Trans], Exp)
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

evaluateBoolUnOp :: ModifyModuleType -> Trans -> (Bool -> Bool) -> Exp -> VerRes ([Trans], Exp)
evaluateBoolUnOp modifyModule op e = do
  v <- evaluateExp modifyModule e
  let bool = case v of
        ETrue -> True
        EFalse -> False
        _ -> error $ "Error in evaluateBoolUnOp: not a bool value: " ++ (show v)

  return $ expFromBool $ op bool

-}
