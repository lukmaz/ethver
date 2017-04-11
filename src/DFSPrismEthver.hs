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
  trs <- verDFSStm modifyModule [("", initGuards, initUpdates)] (SBlock stms)
  mapM_
    (\tr -> modifyModule (\mod -> mod {transs = tr:(transs mod)}))
    trs

---------------
-- verDFSStm --
---------------

-- interprets stm and applies result to every tr in trs
verDFSStm :: ModifyModuleType -> [Trans] -> Stm -> VerRes ([Trans])

verDFSStm modifyModule trs stm = do
  foldM
    (\acc tr -> do
      newTrs <- addDFSStm modifyModule tr stm
      return $ acc ++ newTrs
    )
    []
    trs

---------------
-- addDFSStm --
---------------

-- interprets stm and applies result to a particular tr
addDFSStm :: ModifyModuleType -> Trans -> Stm -> VerRes ([Trans])

addDFSStm modifyModule tr (SBlock []) = do
  return [tr]

addDFSStm modifyModule tr (SBlock (stmH:stmT)) = do
  newTrs <- addDFSStm modifyModule tr stmH
  verDFSStm modifyModule newTrs (SBlock stmT)

addDFSStm modifyModule tr (SAss ident exp) = do
  applyFunToStmWithEvaluation modifyModule tr addAssToTr (SAss ident exp)

addDFSStm modifyModule tr (SArrAss ident index exp) = do
  applyFunToStmWithEvaluation modifyModule tr addAssToTr (SArrAss ident index exp)
  
addDFSStm modifyModule (trName, guards, updates) (SIf cond ifBlock) = do
  -- TODO?: checkCond cond - sprawdzić czy warunek jest jedynego obsłubiwanego typu 
  -- (korzysta tylko ze zmiennych ze zdefiniowaną wartością)

  posTranss <- addDFSStm modifyModule (trName, cond:guards, updates) ifBlock
  let negTranss = [(trName, (negateExp cond):guards, updates)]
  return $ posTranss ++ negTranss

addDFSStm modifyModule (trName, guards, updates) (SIfElse cond ifBlock elseBlock) = do
  posTranss <- addDFSStm modifyModule (trName, cond:guards, updates) ifBlock
  negTranss <- addDFSStm modifyModule (trName, (negateExp cond):guards, updates) elseBlock
  return $ posTranss ++ negTranss

addDFSStm modifyModule _ (SWhile _ _) = do
  error $ "while loop not supported in verDFS"

-------------------------------------------------
-- applyFun with evaluation ---------------------
-- evaluates the argument and applies function --
-------------------------------------------------

-- ZWRACANIE STM DO WYWALENIA
-- TODO: może też zrezygnować ze zwracania Stm?

applyFunToStmWithEvaluation :: ModifyModuleType -> Trans -> (Trans -> Stm -> VerRes [Trans]) -> Stm -> VerRes [Trans]
applyFunToStmWithEvaluation modifyModule tr fun stm = do
  (trs, _) <- evaluateStm modifyModule tr stm
  foldM
    (\acc tr -> do
      newTrs <- fun tr (determineStm tr stm)
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
addVarAssToTr :: Trans -> Stm -> VerRes Trans

addVarAssToTr (trName, guards, updates) (SAss varName exp) = do
  newUpdates <- foldM
    (\acc branch -> do
      partialUpdates <- addAssToUpdatesBranch guards (SAss varName exp) branch
      return $ partialUpdates ++ acc
    )
    []
    updates
  return $ (trName, guards, newUpdates)

addVarAssToTr _ (SArrAss arrName index exp) = do
  error $ "addVarAssToTr should not be called with SArrAss argument (" ++ (show (SArrAss arrName index exp))

-- adds an assignment to a single transition
-- can possibly create longer list of updates in case the array index is not known
addAssToTr :: Trans -> Stm -> VerRes [Trans]

addAssToTr tr (SAss varName exp) = do
  newTr <- addVarAssToTr tr (SAss varName exp)
  return [newTr]


-- TODO DFS: to jest do przeniesienia do evaluateExp?
addAssToTr (trName, guards, updates) (SArrAss (Ident arrName) index exp) = do
  case index of
    {-
    ESender -> do -- TODO: np. trzeba dodać sendera do varsValues
      world <- get
      mod <- modifyModule id
      return $ Map.lookup (whichSender mod) (varsValues world)
    -}
    EInt x -> do
      addAssToTr (trName, guards, updates) $ SAss (Ident $ arrName ++ "_" ++ (show x)) exp
    EVar varName -> do 
      case deduceVarValueFromGuards guards varName of
        (Just (EInt x)) -> do
          addAssToTr (trName, guards, updates) $ SAss (Ident $ arrName ++ "_" ++ (show x)) exp
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
                    (trName, (EEq (EVar varName) (EInt val)):guards, updates) 
                    (SAss (Ident $ arrName ++ "_" ++ (show val)) exp)
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


determineStm :: Trans -> Stm -> Stm

determineStm tr (SAss ident exp) = 
  SAss ident (determineExp tr exp)

determineStm tr (SArrAss ident index exp) = 
  SArrAss ident (determineExp tr index) (determineExp tr exp)

------------------
-- determineExp --
------------------

-- used mainly for EArray: showExp(tab[x]) = tab_2 for x = 2
-- uses x value from guards

determineExp :: Trans -> Exp -> Exp
determineExp (trName, guards, updates) (EArray (Ident arrName) index) = 
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

determineExp _ (EInt x) = EInt x

determineExp (trName, guards, updates) (EVar varIdent) = 
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

evaluateStm :: ModifyModuleType -> Trans -> Stm -> VerRes ([Trans], Stm)

evaluateStm modifyModule tr (SAss ident exp) = do
  (trs, evaluatedExp) <- evaluateExp modifyModule tr exp
  return (trs, SAss ident evaluatedExp)

evaluateStm modifyModule tr (SArrAss ident index exp) = do
  trs <- evaluate2Exp modifyModule tr index exp
  return (trs, SArrAss ident index exp)

evaluate2Exp :: ModifyModuleType -> Trans -> Exp -> Exp -> VerRes [Trans]
evaluate2Exp modifyModule tr exp1 exp2 = do
  (trs, _) <- evaluateExp modifyModule tr exp1
  foldM
    (\acc tr -> do
      -- TODO: nie ma jak wyciągnąć jednego evaluatedExp2, bo jest pętla
      (newTrs, _) <- evaluateExp modifyModule tr exp2
      return $ acc ++ newTrs
    )
    []
    trs

-----------------
-- evaluateExp --
-----------------

evaluateExp :: ModifyModuleType -> Trans -> Exp -> VerRes ([Trans], Exp)
{-
evaluateExp modifyModule tr (EOr e1 e2) = evaluateBoolBinOp modifyModule tr (||) e1 e2
evaluateExp modifyModule tr (EAnd e1 e2) = evaluateBoolBinOp modifyModule tr (&&) e1 e2

evaluateExp modifyModule tr (EEq e1 e2) = evaluateEq modifyModule tr e1 e2
evaluateExp modifyModule tr (ENe e1 e2) = do
  tmp <- evaluateEq modifyModule tr e1 e2
  evaluateBoolUnOp modifyModule tr not tmp

evaluateExp modifyModule tr (ELt e1 e2) = evaluateCompIntBinOp modifyModule tr (<) e1 e2
evaluateExp modifyModule tr (ELe e1 e2) = evaluateCompIntBinOp modifyModule tr (<=) e1 e2
evaluateExp modifyModule tr (EGt e1 e2) = evaluateCompIntBinOp modifyModule tr (>) e1 e2
evaluateExp modifyModule tr (EGe e1 e2) = evaluateCompIntBinOp modifyModule tr (>=) e1 e2
evaluateExp modifyModule tr (EAdd e1 e2) = evaluateArithmIntBinOp modifyModule tr (+) e1 e2
evaluateExp modifyModule tr (ESub e1 e2) = evaluateArithmIntBinOp modifyModule tr (-) e1 e2
evaluateExp modifyModule tr (EMul e1 e2) = evaluateArithmIntBinOp modifyModule tr (*) e1 e2
evaluateExp modifyModule tr (EDiv e1 e2) = evaluateArithmIntBinOp modifyModule tr div e1 e2
evaluateExp modifyModule tr (EMod e1 e2) = evaluateArithmIntBinOp modifyModule tr mod e1 e2

evaluateExp modifyModule tr (ENeg e) = evaluateArithmIntBinOp modifyModule tr (-) (EInt 0) e
evaluateExp modifyModule tr (ENot e) = evaluateBoolUnOp modifyModule tr not e
-}


--DO WYWALENIA?
{-
evaluateExp modifyModule tr (EArray (Ident ident) index) = do
  mod <- modifyModule id
  
  case index of
  
  
  indexEvaluated <- evaluateExp modifyModule index
  case indexEvaluated of 
    EInt indexVal -> evaluateExp modifyModule $ EVar $ Ident $ ident ++ "_" ++ (show indexVal)
    _ -> error $ "Index " ++ (show indexEvaluated) ++ " doesn't evaluate to EInt a)"
-}

evaluateExp modifyModule (trName, guards, updates) (EArray (Ident arrName) index) = do
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


evaluateExp modifyModule tr (EVar ident) = do
  exp <- findVarValue ident
  case exp of 
    Just val -> return ([tr], val)
    Nothing -> return ([tr], EVar ident)

evaluateExp modifyModule tr (EValue) = do
  evaluateExp modifyModule tr (EVar $ Ident sValue)

-- TODO DFS: możliwe, że tu trzeba będzie sprawdzać, czy nie dołożyć sendera do guardsów. albo dodawać zawsze domyślnie
evaluateExp modifyModule tr ESender = do
  world <- get
  mod <- modifyModule id
  case Map.lookup (whichSender mod) (varsValues world) of
    Just x -> return ([tr], x)
    Nothing -> error $ "Variable " ++ (show $ whichSender mod) ++ " not found in varsValues."

evaluateExp modifyModule tr (EStr name) = do
  world <- get
  case Map.lookup name $ playerNumbers world of
    Nothing -> error $ "Player '" ++ name ++ "' not found. (other string constants not supported)"
    Just number -> return ([tr], EInt number)

evaluateExp modifyModule tr (EInt x) = do
  return ([tr], EInt x)

evaluateExp modifyModule tr ETrue = do
  return ([tr], ETrue)

evaluateExp modifyModule tr EFalse = do
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
