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

createSmartTranss :: ModifyModuleType -> Function -> VerRes ()
createSmartTranss modifyModule fun = do
  -- TODO: random condVars
  world <- get
  let condVarsList = Set.toList $ condVars world
  types <- mapM 
    (\var -> do
      res <- findVarType var
      case res of
        Just typ -> return typ
        Nothing -> error "Error in findVarType: var not found."
    )
   condVarsList
  let maxVals = map maxRealValueOfType types
  let valuations = generateAllVals maxVals
  -- TODO: arrays

  mapM_ (createSmartTrans modifyModule fun condVarsList) valuations

createSmartTrans :: ModifyModuleType -> Function -> [Ident] -> [Exp] -> VerRes ()
-- TODO: FunV
createSmartTrans modifyModule (Fun funName args stms) condVarsList vals = do
  -- TODO: co zrobić z probabilistycznymi?
  let guards = map
        (\(varName, val) -> EEq (EVar varName) val)
        -- TODO: arrays
        (zip condVarsList vals)
  
  updates <- foldM
    (\acc stm -> do
      newUpdates <- verSmartStm modifyModule stm
      -- TODO: assumption that newUpdates is a signleton (no probability)
      return $ [(head acc) ++ (head newUpdates)]
    )
    [[]]
    stms
  
  addCustomTrans
    modifyModule
    ""
    1
    1
    guards
    updates
 

---------------------
-- collectCondVars --
---------------------

collectCondVars :: Stm -> VerRes ()

-- TODO: czy używamy SExp?

collectCondVars (SBlock stms) = do
  mapM_ collectCondVars stms

collectCondVars (SAsses asses) = do
  return ()

collectCondVars (SIf cond ifBlock) = do
  collectCondVarsFromExp cond
  collectCondVars ifBlock

collectCondVars (SIfElse cond ifBlock elseBlock) = do
  collectCondVarsFromExp cond
  collectCondVars ifBlock
  collectCondVars elseBlock

collectCondVars (SReturn _) = do
  return ()

-----------------------------
-- collectCondVarsFromExp --
-----------------------------

collectCondVarsFromExp :: Exp -> VerRes ()
collectCondVarsFromExp exp = case exp of
  EOr e1 e2 -> collect2arg e1 e2
  EAnd e1 e2 -> collect2arg e1 e2
  EEq e1 e2 -> collect2arg e1 e2
  ENe e1 e2 -> collect2arg e1 e2
  ELt e1 e2 -> collect2arg e1 e2
  ELe e1 e2 -> collect2arg e1 e2
  EGt e1 e2 -> collect2arg e1 e2
  EGe e1 e2 -> collect2arg e1 e2
  EAdd e1 e2 -> collect2arg e1 e2
  ESub e1 e2 -> collect2arg e1 e2
  EMul e1 e2 -> collect2arg e1 e2
  EDiv e1 e2 -> collect2arg e1 e2
  EMod e1 e2 -> collect2arg e1 e2

  ENeg e -> collectCondVarsFromExp e
  ENot e -> collectCondVarsFromExp e
  
  EArray name index -> collectCondArray name index

  -- TODO: EWait should be moved to Stm
  -- and is not used in contract functions
  -- ECall -> should be moved to Stm
  -- ESend -> should be moved to Stm? (maybe not for checking ret value)
  
  EVar ident -> addCondVar ident

  EValue -> return ()
  ESender -> return ()
  EStr _ -> return ()
  EInt _ -> return ()
  ETrue -> return ()
  EFalse -> return ()

collect2arg :: Exp -> Exp -> VerRes ()
collect2arg e1 e2 = do
  collectCondVarsFromExp e1
  collectCondVarsFromExp e2

collectCondArray :: Ident -> Exp -> VerRes ()
collectCondArray name index = do
  world <- get
  let m = condArrays world
  case Map.lookup name m of 
    Nothing -> put (world {condArrays = (Map.insert name (Set.singleton index) m)})
    Just s -> put (world {condArrays = (Map.insert name (Set.insert index s) m)})


-------------------
-- clearCondVars --
-------------------

clearCondVars :: VerRes ()
clearCondVars = do
  world <- get
  put (world {condVars = Set.empty, condArrays = Map.empty})

-----------------
-- verSmartStm --
-----------------

verSmartStm :: ModifyModuleType -> Stm -> VerRes [[(Ident, Exp)]]

-- TODO: SExp
--verSmartStm modifyModule (SExp exp) = do

verSmartStm modifyModule (SIf cond stm) = do
  result <- evaluateExp cond
  case result of
    ETrue -> verSmartStm modifyModule stm
    EFalse -> return [[]]
    _ -> error $ "Error in verSmartStm(SIf): condition not evaluated to bool: " ++ (show result)

------------------
-- evaluateExp --
------------------

evaluateBoolBinOp :: (Bool -> Bool -> Bool) -> Exp -> Exp -> VerRes Exp
evaluateBoolBinOp op e1 e2 = do
  v1 <- evaluateExp e1
  v2 <- evaluateExp e2
  let bool1 = case v1 of
        ETrue -> True
        EFalse -> False
        _ -> error $ "Error in evaluateBoolBinOp: not a bool value: " ++ (show v1)
  let bool2 = case v2 of
        ETrue -> True
        EFalse -> False
        _ -> error $ "Error in evaluateBoolBinOp: not a bool value: " ++ (show v2)
  
  return $ expFromBool $ op bool1 bool2

evaluateArithmIntBinOp :: (Integer -> Integer -> Integer) -> Exp -> Exp -> VerRes Exp
evaluateArithmIntBinOp op e1 e2 = do
  v1 <- evaluateExp e1
  v2 <- evaluateExp e2
  case intFromExp v1 of 
    Nothing -> error $ "Error in evaluateArithmIntBinOp: not an Int value: " ++ (show v1)
    Just x1 -> case intFromExp v2 of
      Nothing -> error $ "Error in evaluateArithmIntBinOp: not an Int value: " ++ (show v2)
      Just x2 -> return $ expFromInt $ op x1 x2

evaluateCompIntBinOp :: (Integer -> Integer -> Bool) -> Exp -> Exp -> VerRes Exp
evaluateCompIntBinOp op e1 e2 = do
  v1 <- evaluateExp e1
  v2 <- evaluateExp e2
  case intFromExp v1 of 
    Nothing -> error $ "Error in evaluateCompIntBinOp: not an Int value: " ++ (show v1)
    Just x1 -> case intFromExp v2 of
      Nothing -> error $ "Error in evaluateCompIntBinOp: not an Int value: " ++ (show v2)
      Just x2 -> return $ expFromBool $ op x1 x2

evaluateEq :: Exp -> Exp -> VerRes Exp
evaluateEq e1 e2 = do
  v1 <- evaluateExp e1
  v2 <- evaluateExp e2
  if (isBool v1, isBool v2) == (True, True)
    then return $ expFromBool $ v1 == v2
    else case (v1, v2) of
      (EInt x1, EInt x2) -> return $ expFromBool $ x1 == x2
      _ -> error $ "Error in evaluateBoolIntBinOp: not matching types: " ++ (show v1) ++ " and " ++ (show v2)

evaluateBoolUnOp :: (Bool -> Bool) -> Exp -> VerRes Exp
evaluateBoolUnOp op e = do
  v <- evaluateExp e
  let bool = case v of
        ETrue -> True
        EFalse -> False
        _ -> error $ "Error in evaluateBoolUnOp: not a bool value: " ++ (show v)

  return $ expFromBool $ op bool

-- evaluateExp

evaluateExp :: Exp -> VerRes Exp

evaluateExp (EOr e1 e2) = evaluateBoolBinOp (||) e1 e2
evaluateExp (EAnd e1 e2) = evaluateBoolBinOp (&&) e1 e2

evaluateExp (EEq e1 e2) = evaluateEq e1 e2
evaluateExp (ENe e1 e2) = do
  tmp <- evaluateEq e1 e2
  evaluateBoolUnOp not tmp

evaluateExp (ELt e1 e2) = evaluateCompIntBinOp (<) e1 e2
evaluateExp (ELe e1 e2) = evaluateCompIntBinOp (<=) e1 e2
evaluateExp (EGt e1 e2) = evaluateCompIntBinOp (>) e1 e2
evaluateExp (EGe e1 e2) = evaluateCompIntBinOp (>=) e1 e2
evaluateExp (EAdd e1 e2) = evaluateArithmIntBinOp (+) e1 e2
evaluateExp (ESub e1 e2) = evaluateArithmIntBinOp (-) e1 e2
evaluateExp (EMul e1 e2) = evaluateArithmIntBinOp (*) e1 e2
evaluateExp (EDiv e1 e2) = evaluateArithmIntBinOp div e1 e2
evaluateExp (EMod e1 e2) = evaluateArithmIntBinOp mod e1 e2

evaluateExp (ENeg e) = evaluateArithmIntBinOp (-) (EInt 0) e
evaluateExp (ENot e) = evaluateBoolUnOp not e
