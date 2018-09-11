module AuxWorldPrismEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import AbsEthver
import AuxPrismEthver
import AuxEthver
import ConstantsEthver
import WorldPrismEthver

----------
-- Vars --
----------

minValue :: Ident -> VerRes Integer
minValue ident = do
  typ <- findVarType ident
  case typ of
    Just (TUInt x) -> return 0
    Just (TCUInt x) -> return 0
    Just (TSig x) -> return 0
    Just TBool -> return 0
    Just TAddr -> return 0
    Nothing -> error $ "Type of '" ++ (show ident) ++ "' not found"

maxRealValue :: Ident -> VerRes Exp
maxRealValue ident = do
  typ <- findVarType ident
  case typ of
    Just t -> return $ maxRealValueOfType t

maxTypeValue :: Ident -> VerRes Integer
maxTypeValue ident = do
  typ <- findVarType ident
  case typ of
    Just t -> return $ maxTypeValueOfType t

findType :: Exp -> VerRes (Maybe Type)
findType (EInt x) = return $ Just $ TUInt (x + 1)
findType (ETrue) = return $ Just TBool
findType (EFalse) = return $ Just TBool
findType (EVar ident) = findVarType ident
findType (ESender) = do
  world <- get
  let size = fromIntegral $ Map.size $ playerNumbers world 
  return $ Just $ TUInt size
findType (EValue) = do
  findVarType (Ident sValue)
-- strings only used for players names
findType (EStr _) = findType ESender

findVarType :: Ident -> VerRes (Maybe Type)
findVarType ident = do
  world <- get 
  case Map.lookup ident (vars $ blockchain world) of
    Just typ -> return (Just typ)
    Nothing ->  
      case Map.lookup ident (vars $ contract world) of
        Just typ -> return (Just typ)
        Nothing ->  
          case Map.lookup ident (vars $ communication world) of
            Just typ -> return (Just typ)
            Nothing ->  
              case Map.lookup ident (vars $ player0 world) of
                Just typ -> return (Just typ)
                Nothing ->
                  case Map.lookup ident (vars $ player1 world) of
                    Just typ -> return (Just typ)
                    Nothing -> return Nothing

nameOfFunction :: Function -> String
nameOfFunction (Fun (Ident name) _ _) = name
nameOfFunction (FunV (Ident name) _ _) = name
nameOfFunction (FunR (Ident name) _ _ _) = name

-- converts a set of accessed arrays position
-- from (map from array name to positions) to list of pairs (array name, position)
arraysAsList :: Map.Map Ident (Set.Set Exp) -> [(Ident, Exp)]
arraysAsList arrays =
  let 
    -- for an array and set of its accessed positions, creates list of pairs (arrayName, pos)
    expandArray :: Ident -> Set.Set Exp -> [(Ident, Exp)]
    expandArray ident set = Set.toList $ Set.map (\exp -> (ident, exp)) set 

    -- expands all the "arrays"
    expandedArrays :: Map.Map Ident [(Ident, Exp)]
    expandedArrays = Map.mapWithKey expandArray arrays

    -- converts "arrays" from map to list
    arraysList :: [(Ident, Exp)]
    arraysList = concat $ Map.elems $ expandedArrays
  in  
    arraysList

typesFromVarsAndArrays :: [Ident] -> [(Ident, Exp)] -> VerRes [Type]
typesFromVarsAndArrays vars arrays = do
  let firstElements = map (\(Ident ident, _) -> Ident $ ident ++ "_0") arrays
  mapM
    (\var -> do
      res <- findVarType var 
      case res of
        Just typ -> return typ 
        Nothing -> error $ "Error in typesFromVarsAndArrays: var " ++ (show var) ++ " not found."
    )   
    (vars ++ firstElements)

-- TODO: should not be used; use varFromArray instead
arrayToVarOld :: ModifyModuleType -> (Ident, Exp) -> VerRes Ident
arrayToVarOld modifyModule ((Ident arrayName), indexExp) = do
  world <- get
  mod <- modifyModule id

  return $ case indexExp of
    EInt intIndex -> Ident $ arrayName ++ "_" ++ (show intIndex)
    ESender ->
      case Map.lookup (whichSender mod) (varsValues world) of
        Just (EInt value) -> Ident $ arrayName ++ "_" ++ (show value)
        Just _ -> error $ "arrayToVarOld: value of 'sender' is not of type EInt"
        Nothing -> error $ "arrayToVarOld: array[sender] used, but 'sender' is not in varsValues"
    EVar varName ->
      case Map.lookup varName (varsValues world) of
        Just (EInt value) -> Ident $ arrayName ++ "_" ++ (show value)
        Just _ -> error $ "arrayToVarOld: value of '" ++ (unident varName) ++ "' value is not of type EInt"
        Nothing -> error $ "arrayToVarOld: array[" ++ (unident varName) ++ "] used, but '" ++ (unident varName) 
          ++ "' is not in varsValues"
    
varFromArray :: Exp -> VerRes Exp
varFromArray (EArray (Ident varName) index) = do
  world <- get 
  let 
    actualIndex = case index of
      EInt x -> Just x
      ESender -> senderNumber world
      _ -> error $ (show index) ++ ": index can be only an integer or msg.sender"
  case actualIndex of
    Just x -> return $ EVar $ Ident $ varName ++ "_" ++ (show x)
    _ -> error $ show (EArray (Ident varName) index) ++ ": senderNumber not set in World"

toVar :: Exp -> VerRes Exp
toVar (EVar v) = return $ EVar v

toVar (EArray arrIdent index) = varFromArray (EArray arrIdent index)

toVar ESender = do
  world <- get
  case senderNumber world of
    Just x -> return $ EInt x
    _ -> error $ "senderNumber world not defined"

toVar exp = error $ "toVar '" ++ show exp ++ "' not implemented"

-----------
-- Users --
-----------

addUser :: UserDecl -> VerRes ()
addUser (UDec name) = do
  addPlayer name

-------------------
-- applyToBranch --
-------------------

applyToBranch :: ([(Ident, Exp)] -> [(Ident, Exp)]) -> Branch -> Branch
applyToBranch f (br, liv) = (f br, liv)

-----------
-- Trans --
-----------

addTransToNewState :: ModifyModuleType -> String -> [Exp] -> [Branch] -> VerRes ()
addTransToNewState modifyModule transName guards updates = do
  mod <- modifyModule id
  let newState = numStates mod + 1
  addCustomTrans modifyModule transName (currState mod) newState guards updates
  _ <- modifyModule (setCurrState newState)
  _ <- modifyModule (setNumStates newState)
  return ()

addCustomTrans :: ModifyModuleType -> String -> Integer -> Integer -> [Exp] -> [Branch] -> VerRes ()
addCustomTrans modifyModule transName fromState toState guards updates = do
  mod <- modifyModule id
  let newTrans = newCustomTrans (stateVar mod) transName fromState toState guards updates
  _ <- modifyModule (addTransToModule newTrans)
  return ()

addFirstCustomTrans :: ModifyModuleType -> String -> Integer -> Integer -> [Exp] -> [Branch] -> VerRes ()
addFirstCustomTrans modifyModule transName fromState toState guards updates = do
  mod <- modifyModule id
  let newTrans = newCustomTrans (stateVar mod) transName fromState toState guards updates
  _ <- modifyModule (addFirstTransToModule newTrans)
  return ()


addTransNoState :: ModifyModuleType -> String -> [Exp] -> [Branch] -> VerRes ()
addTransNoState modifyModule transName guards updates = do
  mod <- modifyModule id
  let newTrans = newTransNoState transName guards updates
  _ <- modifyModule (addTransToModule newTrans)
  return ()

newCustomTrans :: String -> String -> Integer -> Integer -> [Exp] -> [Branch] -> Trans
newCustomTrans stateVar transName fromState toState guards updates =
  newTransNoState
    transName
    ((EEq (EVar (Ident stateVar)) (EInt fromState)):guards)
    -- TODO: Alive?
    (map (applyToBranch ((Ident stateVar, EInt toState):)) updates)
  

newTransNoState :: String -> [Exp] -> [Branch] -> Trans
newTransNoState transName guards updates =
  (transName, guards, updates)

addTransToModule :: Trans -> Module -> Module
addTransToModule tr mod = 
  mod {transs = tr:(transs mod)}

addFirstTransToModule :: Trans -> Module -> Module
addFirstTransToModule tr mod =
  mod {transs = (transs mod) ++ [tr]}

-- TODO: similar things are in verFunExecute for contract
addCommunicateOnePlayer :: Ident -> [Arg] -> Integer -> VerRes ()
addCommunicateOnePlayer funName args playerNumber = do
  mod <- modifyCommunication id
  let 
    newState = numStates mod + 1 
    updates0 = [[(iCommSender, EInt playerNumber)]]
    addAssignment acc (Ar (TCUInt _) varName) = acc
        ++ [(createCoArgumentName sIdSuffix funName varName, 
              EVar $ createScenarioArgumentName sIdSuffix funName varName playerNumber)]
        -- ++ [(createCoArgumentName "" funName varName, 
        --       EVar $ createScenarioArgumentName "" funName varName playerNumber)]
    addAssignment acc (Ar _ varName) = acc ++
        [(createCoArgumentName "" funName varName, 
          EVar $ createScenarioArgumentName "" funName varName playerNumber)]
  -- TODO: Alive?
    updates = [(foldl addAssignment [] args, [Alive])]

  -- first trans to set sender
  addCustomTrans
    modifyCommunication
    (sCommunicatePrefix ++ (unident funName) ++ (show playerNumber))
    1   
    newState
    []  
    [(head updates0, [Alive])]

  -- second trans to set arguments
  addCustomTrans
    modifyCommunication
    ""
    newState
    (newState + 1)
    [EEq (EVar iCommSender) (EInt playerNumber)]
    updates


----------------------
-- Critical section --
----------------------

-- converts all commands in a module by adding critical section stuff
addCS :: Module -> Module
addCS mod = 
  mod { transs = reverse $ 
    foldl
      (\acc tr -> ((setCS (number mod) tr):(unsetCS (number mod) tr):acc))
      []
      (transs mod)
  }
  
setCS :: Integer -> Trans -> Trans
setCS number (_, guards, _) = 
  (
    "",
    (ENot $ EVar iCriticalSection0)
      :(ENot $ EVar iCriticalSection1)
      :guards,
    [([(Ident $ sCriticalSection ++ (show number), ETrue)], [Alive])]
  )

unsetCS :: Integer -> Trans -> Trans
unsetCS number (transName, guards, updates) =
  (
    transName,
    -- critical section
    --(EVar $ Ident $ sCriticalSection ++ (show number))
    (EEq (EVar iContrState) (EInt 1))
      :(EEq (EVar iCommState) (EInt 1))
      :guards,
    -- critical section
    --(map ((Ident $ sCriticalSection ++ (show number), EFalse):) updates)
    updates
  )

--------------------------------
-- Alternative approach to CS --
--------------------------------


-- converts all commands in a module by adding critical section stuff
addCS2 :: Module -> Module
addCS2 mod = 
  mod { transs = reverse -- $ setCS2 (number mod) ++  (... critical section )
    (foldl
      (\acc tr -> ((unsetCS (number mod) tr):acc))
      []
      (transs mod)
    )
  }

-- only two commands for the whole scenario
setCS2 :: Integer -> [Trans]
setCS2 number  = 
  [(
    "",
    [ENot $ EVar iCriticalSection0,
      ENot $ EVar iCriticalSection1,
      EGt (EVar $ Ident $ sStatePrefix ++ (show number)) (EInt 0)],
    [([(Ident $ sCriticalSection ++ (show number), ETrue)], [Alive])]
  ),
  (
    "",
    [EVar $ Ident $ sCriticalSection ++ (show number),
    -- one line quickfix:
      EEq (EVar iContrState) (EInt 1)],
    [([(Ident $ sCriticalSection ++ (show number), EFalse)], [Alive])]
  )]

------------------------------
-- Adversarial transactions --
------------------------------

advUpdates :: Bool -> Integer -> Ident -> [Arg] -> [Exp] -> [[(Ident, Exp)]]
advUpdates withVal number funName args valList =
  let 
    prefix :: [(String, String)] -> [(String, String)]
    prefix x = if withVal then (unident funName ++ "_" ++ sValue, ""):x else x
    aux :: Arg -> (String, String)
    aux (Ar (TCUInt _) (Ident ident)) = (ident, sIdSuffix)
    aux (Ar _ (Ident ident)) = (ident, "")
    varNames = prefix (map aux args) 
  in
    [   
      map 
        (\((varName, suffix), v) -> (createScenarioArgumentName suffix funName (Ident varName) number, v)) 
        (zip varNames valList)
    ]   

-- moved from verScenarios
addAdversarialBlockchainTranss :: VerRes()
addAdversarialBlockchainTranss = do
  world <- get
  addTransNoState
    modifyBlockchain
    (sTimelockStep)
    (   
      {-(EOr 
        (EAnd (EVar $ Ident $ sWaits ++ "0") (EVar $ Ident $ sWaits ++ "1")) 
        (EOr 
          (EAnd (EVar $ Ident $ sWaits ++ "0") (EEq (EVar $ Ident $ sAdversaryFlag) (EInt 1)))
          (EAnd (EVar $ Ident $ sWaits ++ "1") (EEq (EVar $ Ident $ sAdversaryFlag) (EInt 0)))
        )
      ) : -} 
        (ELt (EVar $ Ident $ sTimeElapsed) (EVar $ Ident $ sMaxTime))
        : (Map.elems $ Map.map
            (\fun -> ENe 
              (EVar $ Ident $ (nameOfFunction fun) ++ sStatusSuffix ++ "0")
              (EVar iTBroadcast)
            )   
            (contractFuns world)
          )   
        ++ (Map.elems $ Map.map
            (\fun -> ENe 
              (EVar $ Ident $ (nameOfFunction fun) ++ sStatusSuffix ++ "1")
              (EVar iTBroadcast)
            )   
            (contractFuns world)
          )   
    )   
    -- TODO: Alive?
    [([(Ident sTimeElapsed, EAdd (EVar $ Ident sTimeElapsed) (EInt 1))], [Alive])]

addAdversarialContrTranss :: Contract -> VerRes ()
addAdversarialContrTranss (Contr _ _ funs) =
  addAdversarialTranss funs sBroadcastPrefix iContrState

addAdversarialCommTranss :: Communication -> VerRes ()
addAdversarialCommTranss (Comm _ funs) =
  addAdversarialTranss funs sCommunicatePrefix iCommState


addAdversarialTranss :: [Function] -> String -> Ident -> VerRes ()
addAdversarialTranss funs whichPrefix whichState = do
  mapM_ (addAdversarialTranssToPlayer modifyPlayer0 whichPrefix whichState) funs
  mapM_ (addAdversarialTranssToPlayer modifyPlayer1 whichPrefix whichState) funs


addAdversarialTranssToPlayer :: ModifyModuleType -> String -> Ident -> Function -> VerRes ()

addAdversarialTranssToPlayer modifyModule whichPrefix whichState (FunV (Ident funName) args _) = do
  mod <- modifyModule id  
  let valName = Ident $ funName  ++ sValueSuffix ++ (show $ number mod)
  maxValVal <- maxRealValue valName
  let maxValsList = generateValsList maxValVal args
  generateAdvTranss modifyModule whichPrefix whichState True (-1) funName args maxValsList

addAdversarialTranssToPlayer modifyModule whichPrefix whichState (Fun (Ident funName) args x) = 
  addAdversarialTranssToPlayer modifyModule whichPrefix whichState (FunL (-1) (Ident funName) args x)

addAdversarialTranssToPlayer modifyModule whichPrefix whichState (FunL limit (Ident funName) args _) = do
  let maxValsList = generateValsListNoVal args
  generateAdvTranss modifyModule whichPrefix whichState False limit funName args maxValsList


generateAdvTranss :: ModifyModuleType -> String -> Ident -> Bool -> Integer -> String -> [Arg] -> [[Exp]] -> VerRes ()
generateAdvTranss modifyModule whichPrefix whichState withVal limit funName args maxes = do
  mod <- modifyModule id
  let runsIdent = Ident $ funName ++ sRunsSuffix ++ (show $ number mod)
  case maxes of
    [] ->
      addTransNoState
        modifyModule
        (whichPrefix ++ funName ++ (show $ number mod))
        (
          [   
            -- critical section
            -- ENot $ EVar $ Ident $ sCriticalSection ++ (show $ 1 - (number mod)),
            EEq (EVar iContrState) (EInt 1), 
            EEq (EVar iCommState) (EInt 1), 
            EEq (EVar $ Ident $ sStatePrefix ++ (show $ number mod)) (EInt (-1))
          ]
          ++ 
          (if (limit > -1) then [ELt (EVar runsIdent) (EInt limit)] else [])
        )
        -- TODO: Alive?
        [(if (limit > -1) then [(runsIdent, EAdd (EVar runsIdent) (EInt 1))] else [], [Alive])]
    maxValsList -> do
      forM_
        maxValsList
        (\vals -> addTransNoState
          modifyModule
          (whichPrefix ++ funName ++ (show $ number mod))
          (
            [
              -- critical section
              -- ENot $ EVar $ Ident $ sCriticalSection ++ (show $ 1 - (number mod)),
              EEq (EVar iContrState) (EInt 1),
              EEq (EVar iCommState) (EInt 1),
              EEq (EVar $ Ident $ sStatePrefix ++ (show $ number mod)) (EInt (-1))
            ]
            ++ 
            (if (limit > -1) then [ELt (EVar runsIdent) (EInt limit)] else [])
          )
          -- TODO: Alive?
          (map 
            (\x -> (x ++ (if (limit > -1) then [(runsIdent, EAdd (EVar runsIdent) (EInt 1))] else []), [Alive]))
            (advUpdates withVal (number mod) (Ident funName) args vals)
          )
        )


---------------------
-- MONEY TRANSFERS --
---------------------

-- TODO: one MAX_USER_BALANCE for all users
transferFromContract :: Ident -> Exp -> VerRes ()
transferFromContract to value = do
  transferMoney iContractBalance to (EVar iMaxUserBalance) value
  
burnMoney :: Exp -> VerRes ()
burnMoney value = do
  addTransToNewState
    modifyContract
    ""
    [EGe (EVar iContractBalance) value]
    [([(iContractBalance, ESub (EVar iContractBalance) value)], [Alive])]


transferMoney :: Ident -> Ident -> Exp -> Exp -> VerRes ()
transferMoney from to maxTo value = do
  mod <- modifyContract id
  let newState = numStates mod + 1
  
  -- fail if not enough money or not enough max balance of recipient
  addCustomTrans 
    modifyContract 
    "" 
    (currState mod) 
    newState 
    [EOr (ELt (EVar from) value) (EGt (EAdd (EVar to) value) maxTo)]
    [([], [Alive])]
  
  -- succeed if enough money and max balance of recipient high enough
  addTransToNewState
    --TODO: czy to przypadkiem nie ma być w BC?
    modifyContract
    ""
    [EGe (EVar from) value, ELe (EAdd (EVar to) value) maxTo]
    -- TODO: Alive?
    [([(from, ESub (EVar from) value), (to, EAdd (EVar to) value)], [Alive])]

-- TODO: one MAX_USER_BALANCE for all users
smartTransferFromContract :: Ident -> Exp -> VerRes [[(Ident, Exp)]]
smartTransferFromContract to value = do
  smartTransferMoney iContractBalance to (EVar iMaxUserBalance) value

smartTransferMoney :: Ident -> Ident -> Exp -> Exp -> VerRes [[(Ident, Exp)]]
smartTransferMoney from to maxTo value = do
  addGuard (EGe (EVar from) value)
  addGuard (ELe (EAdd (EVar to) value) maxTo)
  return [[(from, ESub (EVar from) value), (to, EAdd (EVar to) value)]]

-----------
-- DEBUG --
-----------

debugMapAux :: (Show a, Show b) => Map.Map a b -> String
debugMapAux myMap =
  let eee = foldl 
        (\acc (ident, exp) -> acc ++ "(" ++ (show ident) ++ ", " ++ (show exp) ++ ")\n" ) 
        ""  
        (Map.toList $ myMap)
  in eee ++ "\n"

debugSetAux :: (Show a) => Set.Set a -> String
debugSetAux mySet =
  let eee = foldl 
        (\acc x -> acc ++ (show x) ++ "\n" ) 
        ""  
        (Set.toList $ mySet)
  in eee ++ "\n"

debugVarsValues :: VerRes ()
debugVarsValues = do
  world <- get
  error $ "varsValues:\n" ++ (debugMapAux $ varsValues world)

debugCondVars :: VerRes ()
debugCondVars = do
  world <- get
  error $ "condVars:\n" ++ (debugSetAux $ condVars world)

debugCondArrays :: VerRes ()
debugCondArrays = do
  world <- get
  error $ "condArrays:\n" ++ (debugMapAux $ condArrays world)

debugVars :: VerRes ()
debugVars = do
  world <- get
  error $ "vars:\n" ++ 
    (debugMapAux $ vars $ blockchain world)
    ++ (debugMapAux $ vars $ contract world)
    ++ (debugMapAux $ vars $ communication world)
    ++ (debugMapAux $ vars $ player0 world)
    ++ (debugMapAux $ vars $ player1 world)

