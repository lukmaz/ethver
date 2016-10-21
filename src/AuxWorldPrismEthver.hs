module AuxWorldPrismEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map

import AbsEthver
import AuxPrismEthver
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
    Just (TRUInt x) -> return 0
    Just TBool -> return 0

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

-----------
-- Users --
-----------

addUser :: UserDecl -> VerRes ()
addUser (UDec name) = do
  addPlayer name


-----------
-- Trans --
-----------

addTransToNewState :: ModifyModuleType -> String -> [Exp] -> [[(Ident, Exp)]] -> VerRes ()
addTransToNewState modifyModule transName guards updates = do
  mod <- modifyModule id
  let newState = numStates mod + 1
  addCustomTrans modifyModule transName (currState mod) newState guards updates
  _ <- modifyModule (setCurrState newState)
  _ <- modifyModule (setNumStates newState)
  return ()

addCustomTrans :: ModifyModuleType -> String -> Integer -> Integer -> [Exp] -> [[(Ident, Exp)]] -> VerRes ()
addCustomTrans modifyModule transName fromState toState guards updates = do
  mod <- modifyModule id
  let newTrans = newCustomTrans (stateVar mod) transName fromState toState guards updates
  _ <- modifyModule (addTransToModule newTrans)
  return ()

addFirstCustomTrans :: ModifyModuleType -> String -> Integer -> Integer -> [Exp] -> [[(Ident, Exp)]] -> VerRes ()
addFirstCustomTrans modifyModule transName fromState toState guards updates = do
  mod <- modifyModule id
  let newTrans = newCustomTrans (stateVar mod) transName fromState toState guards updates
  _ <- modifyModule (addFirstTransToModule newTrans)
  return ()


addTransNoState :: ModifyModuleType -> String -> [Exp] -> [[(Ident, Exp)]] -> VerRes ()
addTransNoState modifyModule transName guards updates = do
  mod <- modifyModule id
  let newTrans = newTransNoState transName guards updates
  _ <- modifyModule (addTransToModule newTrans)
  return ()

newCustomTrans :: String -> String -> Integer -> Integer -> [Exp] -> [[(Ident, Exp)]] -> Trans
newCustomTrans stateVar transName fromState toState guards updates =
  newTransNoState
    transName
    ((EEq (EVar (Ident stateVar)) (EInt fromState)):guards)
    (map ((Ident stateVar, EInt toState):) updates)
  

newTransNoState :: String -> [Exp] -> [[(Ident, Exp)]] -> Trans
newTransNoState transName guards updates =
  (transName, guards, updates)

addTransToModule :: Trans -> Module -> Module
addTransToModule tr mod = 
  mod {transs = tr:(transs mod)}

addFirstTransToModule :: Trans -> Module -> Module
addFirstTransToModule tr mod =
  mod {transs = (transs mod) ++ [tr]}

addCommunicateOnePlayer :: Ident -> [Arg] -> Integer -> VerRes ()
addCommunicateOnePlayer funName args playerNumber = do
  mod <- modifyCommunication id
  let newState = numStates mod + 1 

  let updates0 = [[(iCommSender, EInt playerNumber)]]
  let addAssignment acc (Ar _ (Ident varName)) = acc ++
        [(Ident $ unident funName ++ "_" ++ varName, 
          EVar $ Ident $ unident funName ++ "_" ++ varName ++ (show playerNumber))]
  let updates = [foldl addAssignment (head updates0) args]

  addCustomTrans
    modifyCommunication
    (sCommunicatePrefix ++ (unident funName) ++ (show playerNumber))
    1   
    newState
    []  
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
    [[(Ident $ sCriticalSection ++ (show number), ETrue)]]
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
    [[(Ident $ sCriticalSection ++ (show number), ETrue)]]
  ),
  (
    "",
    [EVar $ Ident $ sCriticalSection ++ (show number),
    -- one line quickfix:
      EEq (EVar iContrState) (EInt 1)],
    [[(Ident $ sCriticalSection ++ (show number), EFalse)]]
  )]

------------------------------
-- Adversarial transactions --
------------------------------

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
  let valName = Ident $ funName ++ sValueSufix ++ (show $ number mod)
  maxValVal <- maxRealValue valName
  let maxValsList = generateValsList maxValVal args
  generateAdvTranss modifyModule whichPrefix whichState True funName args maxValsList

addAdversarialTranssToPlayer modifyModule whichPrefix whichState (Fun (Ident funName) args _) = do
  let maxValsList = generateValsListNoVal args
  generateAdvTranss modifyModule whichPrefix whichState False funName args maxValsList

generateAdvTranss :: ModifyModuleType -> String -> Ident -> Bool -> String -> [Arg] -> [[Exp]] -> VerRes ()
generateAdvTranss modifyModule whichPrefix whichState withVal funName args maxes = do
  mod <- modifyModule id
  case maxes of
    [] ->
      addTransNoState
        modifyModule
        (whichPrefix ++ funName ++ (show $ number mod))
        [   
          -- critical section
          -- ENot $ EVar $ Ident $ sCriticalSection ++ (show $ 1 - (number mod)),
          EEq (EVar iContrState) (EInt 1), 
          EEq (EVar iCommState) (EInt 1), 
          EEq (EVar $ Ident $ sStatePrefix ++ (show $ number mod)) (EInt (-1))
        ]   
        [[]]
    maxValsList ->
      forM_
        maxValsList
        (\vals -> addTransNoState
          modifyModule
          (whichPrefix ++ funName ++ (show $ number mod))
          [
            -- critical section
            -- ENot $ EVar $ Ident $ sCriticalSection ++ (show $ 1 - (number mod)),
            EEq (EVar iContrState) (EInt 1),
            EEq (EVar iCommState) (EInt 1),
            EEq (EVar $ Ident $ sStatePrefix ++ (show $ number mod)) (EInt (-1))
          ]
          (advUpdates withVal (number mod) funName args vals)
        )


---------------------
-- MONEY TRANSFERS --
---------------------

-- TODO: one MAX_USER_BALANCE for all users
transferFromContract :: Ident -> Exp -> VerRes ()
transferFromContract to value = do
  transferMoney iContractBalance to (EVar iMaxUserBalance) value
  

transferMoney :: Ident -> Ident -> Exp -> Exp -> VerRes ()
transferMoney from to maxTo value = do
  addTransToNewState
    --TODO: czy to przypadkiem nie ma być w BC?
    modifyContract
    ""
    [EGe (EVar from) value, ELe (EAdd (EVar to) value) maxTo]
    [[(from, ESub (EVar from) value), (to, EAdd (EVar to) value)]]

