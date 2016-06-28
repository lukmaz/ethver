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
    (ENot $ EVar $ Ident "critical_section0")
      :(ENot $ EVar $ Ident "critical_section1")
      :guards,
    [[(Ident $ "critical_section" ++ (show number), ETrue)]]
  )

unsetCS :: Integer -> Trans -> Trans
unsetCS number (transName, guards, updates) =
  (
    transName,
    (EVar $ Ident $ "critical_section" ++ (show number))
      :(EEq (EVar $ Ident "cstate") (EInt 1))
      :guards,
    (map ((Ident $ "critical_section" ++ (show number), EFalse):) updates)
  )

---------------------
-- MONEY TRANSFERS --
---------------------

-- TODO: one MAX_USER_BALANCE for all users
transferFromContract :: Ident -> Exp -> VerRes ()
transferFromContract to value = do
  transferMoney (Ident "contract_balance") to (EVar iMaxUserBalance) value
  

transferMoney :: Ident -> Ident -> Exp -> Exp -> VerRes ()
transferMoney from to maxTo value = do
  addTransToNewState
    --TODO: czy to przypadkiem nie ma być w BC?
    modifyContract
    ""
    [EGe (EVar from) value, ELe (EAdd (EVar to) value) maxTo]
    [[(from, ESub (EVar from) value), (to, EAdd (EVar to) value)]]

