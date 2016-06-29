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
          case Map.lookup ident (vars $ player0 world) of
            Just typ -> return (Just typ)
            Nothing ->
              case Map.lookup ident (vars $ player1 world) of
                Just typ -> return (Just typ)
                Nothing -> return Nothing

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
    (EVar $ Ident $ sCriticalSection ++ (show number))
      :(EEq (EVar iContrState) (EInt 1))
      :guards,
    (map ((Ident $ sCriticalSection ++ (show number), EFalse):) updates)
  )

------------------------------
-- Adversarial transactions --
------------------------------
addAdversarialTranssToPlayer :: ModifyModuleType -> Function -> VerRes ()
addAdversarialTranssToPlayer modifyModule (FunV (Ident funName) args _) = do
  mod <- modifyModule id  
  let valName = Ident $ funName ++ sValueSufix ++ (show $ number mod)
  maxValVal <- maxRealValue valName
  let maxValsList = generateValsList maxValVal args
  generateAdvTranss modifyModule True funName args maxValsList

addAdversarialTranssToPlayer modifyModule (Fun (Ident funName) args _) = do
  let maxValsList = generateValsListNoVal args
  generateAdvTranss modifyModule False funName args maxValsList

generateAdvTranss :: ModifyModuleType -> Bool -> String -> [Arg] -> [[Exp]] -> VerRes ()
generateAdvTranss modifyModule withVal funName args maxes = do
  mod <- modifyModule id
  case maxes of
    [] ->
      addTransNoState
        modifyModule
        (sBroadcastPrefix ++ funName ++ (show $ number mod))
        [   
          ENot $ EVar $ Ident $ sCriticalSection ++ (show $ 1 - (number mod)),
          EEq (EVar iContrState) (EInt 1), 
          EEq (EVar $ Ident $ sStatePrefix ++ (show $ number mod)) (EInt (-1))
        ]   
        [[]]
    maxValsList ->
      forM_
        maxValsList
        (\vals -> addTransNoState
          modifyModule
          (sBroadcastPrefix ++ funName ++ (show $ number mod))
          [
            ENot $ EVar $ Ident $ sCriticalSection ++ (show $ 1 - (number mod)),
            EEq (EVar iContrState) (EInt 1),
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

