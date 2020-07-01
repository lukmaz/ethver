module AuxWorldPrismEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import GHC.Stack

import AbsEthver
import AuxPrismEthver
import AuxEthver
import ConstantsEthver
import WorldPrismEthver

----------
-- Vars --
----------

maxRealValue :: Ident -> VerRes Exp
maxRealValue ident = do
  typ <- findVarType ident
  case typ of
    Just t -> return $ maxRealTypeValue t
    _ -> error $ "Cannot findVarType of " ++ unident ident

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
  let
    listFromModule :: (VerWorld -> Module) -> [(Ident, Type)]
    listFromModule mod = (Map.toList $ vars $ mod world) ++ (Map.toList $ globalCommitments $ mod world) ++
      (Map.toList $ globalSignatures $ mod world)
    l = foldl 
      (\acc m -> acc ++ listFromModule m) 
      []
      [blockchain, contract, communication, player0, player1]
    newMap = Map.fromList l
  return $ Map.lookup ident newMap

isGlobalCommitmentIdent :: Ident -> Bool
isGlobalCommitmentIdent ident =
  (init $ unident ident) == (sGlobalCommitments ++ "_")

isGlobalSignatureIdent :: Ident -> Bool
isGlobalSignatureIdent ident = 
  (init $ unident ident) == (sGlobalSignatures ++ "_")

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

toVar (EInt x) = return $ EInt x

toVar (EHashOf x) = return x

toVar exp = error $ "toVar '" ++ show exp ++ "' not implemented"

-----------
-- Users --
-----------

addUser :: UserDecl -> VerRes ()
addUser (UDec name) = do
  addPlayer name

-----------
-- Trans --
-----------

-- similar to verFunExecute for contract
addCommunicateOnePlayer :: Ident -> [Arg] -> Integer -> VerRes ()
addCommunicateOnePlayer funName args playerNumber = do
  mod <- modifyCommunication id
  let 
    newState = numStates mod + 1 
    updates0 = [[(iCommSender, EInt playerNumber)]]
    addAssignment acc (Ar (TCUInt _) varName) = acc
        ++ [(createCoArgumentName "" funName varName, 
              EVar $ createScenarioArgumentName "" funName varName playerNumber)]
    addAssignment acc (Ar _ varName) = acc ++
        [(createCoArgumentName "" funName varName, 
          EVar $ createScenarioArgumentName "" funName varName playerNumber)]
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
    (EEq (EVar iContrState) (EInt 1))
      :(EEq (EVar iCommState) (EInt 1))
      :guards,
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
    aux (Ar (TCUInt _) (Ident ident)) = (ident, "")
    aux (Ar _ (Ident ident)) = (ident, "")
    varNames = prefix (map aux args) 
  in
    [   
      map 
        (\((varName, suffix), v) -> (createScenarioArgumentName suffix funName (Ident varName) number, v)) 
        (zip varNames valList)
    ]   

-- adds a single trans to Blockchain module to disallow time step when a transaction is being broadcast
addAdversarialBlockchainTranss :: VerRes()
addAdversarialBlockchainTranss = do
  world <- get
  addTransNoState
    modifyBlockchain
    (sTimelockStep)
    (   
        (ELt (EVar $ Ident $ sTimeElapsed) (EVar $ Ident $ sMaxTime))
        : (Map.elems $ Map.map
            (\fun -> ENe 
              (EVar $ Ident $ unident (getFunName fun) ++ sStatusSuffix ++ "0")
              (EVar iTBroadcast)
            )   
            (contractFuns world)
          )   
        ++ (Map.elems $ Map.map
            (\fun -> ENe 
              (EVar $ Ident $ unident (getFunName fun) ++ sStatusSuffix ++ "1")
              (EVar iTBroadcast)
            )   
            (contractFuns world)
          )   
    )   
    [([(Ident sTimeElapsed, EAdd (EVar $ Ident sTimeElapsed) (EInt 1))], [Alive])]

addAdversarialContrTranss :: Contract -> VerRes ()
addAdversarialContrTranss (Contr _ _ _ funs) =
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
  generateAdvTranssNew modifyModule whichPrefix whichState True (-1) funName args

addAdversarialTranssToPlayer modifyModule whichPrefix whichState (Fun (Ident funName) args _) = do
  generateAdvTranssNew modifyModule whichPrefix whichState False (-1) funName args

generateAdvTranssNew :: ModifyModuleType -> String -> Ident -> Bool -> Integer -> String -> [Arg] -> VerRes ()
generateAdvTranssNew modifyModule whichPrefix whichState withVal limit funName argsOrig = do
  mod <- modifyModule id
  let cmtVar = Ident $ sGlobalCommitments ++ "_" ++ (show $ number mod)
  world <- get
  typ <- findVarType cmtVar

  let 
    args = filter 
      (\x -> case x of
        Ar (TCUInt _) _ -> False
        Ar (TSig _) _ -> False
        _ -> True
      )
      argsOrig

    (extraGuardsCmt, extraUpdatesCmt) =
      if commitmentInArguments (Fun (Ident "") argsOrig []) 
        then 
          case cmtRange world of
            Just range ->
              let 
                cmtArgVar = Ident $ (unident $ commitmentFromArguments (Fun (Ident "") argsOrig []))
                    ++ (show $ number mod)
              in
                ([ELt (EVar cmtVar) (EInt $ range)], [(cmtArgVar, EInt $ number mod)])
        else
          ([], [])
    
    (extraGuardsSig, extraUpdatesSig) =
      if signatureInArguments (Fun (Ident "") argsOrig []) 
        then 
          case cmtRange world of
            Just range ->
              let 
                sigArgVar = Ident $ (unident $ signatureFromArguments (Fun (Ident "") argsOrig []))
                    ++ (show $ number mod)
              in
                ([], [(sigArgVar, EInt $ number mod)])
        else
          ([], [])
    
  generateAdvTranssAux 
    modifyModule 
    whichPrefix 
    whichState 
    withVal 
    limit 
    funName 
    args 
    (extraGuardsCmt ++ extraGuardsSig)
    (extraUpdatesCmt ++ extraUpdatesSig)

hashGuards :: Integer -> [Arg] -> [Exp] -> [Exp]
hashGuards cmtRange args vals =
  let 
    hashPairs = filter
      (\(Ar typ _, val) -> typ == THash)
      (zip args vals)
  in
    map
      (\(Ar _ _, EInt x) -> ELe (EVar $ Ident $ sGlobalCommitments ++ "_" ++ show x) (EInt cmtRange))
      hashPairs

generateAdvTranssAux :: ModifyModuleType -> String -> Ident -> Bool -> Integer -> String -> [Arg] -> [Exp] -> [(Ident, Exp)] -> VerRes ()
generateAdvTranssAux modifyModule whichPrefix whichState withVal limit funName args extraGuards extraUpdates = do
  mod <- modifyModule id
  world <- get
  let valName = Ident $ funName ++ sValueSuffix ++ (show $ number mod)
  maxes <- if withVal
    then do
      maxValVal <- maxRealValue valName
      return $ generateValsList maxValVal args
    else do 
      return $ generateValsListNoVal args

  let 
    runsIdent = Ident $ funName ++ sRunsSuffix ++ (show $ number mod)
    range = case cmtRange world of
      Just r -> r
      Nothing -> 0

  case maxes of
    [] ->
      addTransNoState
        modifyModule
        (whichPrefix ++ funName ++ (show $ number mod))
        (
          [   
            EEq (EVar iContrState) (EInt 1), 
            EEq (EVar iCommState) (EInt 1), 
            EEq (EVar $ Ident $ sStatePrefix ++ (show $ number mod)) (EInt (-1))
          ]
          ++ 
          extraGuards
          ++ 
          (if (limit > -1) then [ELt (EVar runsIdent) (EInt limit)] else [])
        )
        [(extraUpdates ++ (if (limit > -1) then [(runsIdent, EAdd (EVar runsIdent) (EInt 1))] else []), [Alive])]
    maxValsList -> do
      forM_
        maxValsList
        (\vals -> addTransNoState
          modifyModule
          (whichPrefix ++ funName ++ (show $ number mod))
          (
            [
              EEq (EVar iContrState) (EInt 1),
              EEq (EVar iCommState) (EInt 1),
              EEq (EVar $ Ident $ sStatePrefix ++ (show $ number mod)) (EInt (-1))
            ]
            ++
            (hashGuards 
              range 
              args 
              (if withVal then (tail vals) else vals)
            )
            ++ 
            extraGuards
            ++
            (if (limit > -1) then [ELt (EVar runsIdent) (EInt limit)] else [])
          )
          (map 
            (\x -> (x ++ extraUpdates ++ (if (limit > -1) then [(runsIdent, EAdd (EVar runsIdent) (EInt 1))] else []), [Alive]))
            (advUpdates withVal (number mod) (Ident funName) args vals)
          )
        )

advTransAux :: ModifyModuleType -> [Exp] -> [Branch] -> VerRes ()
advTransAux modifyModule guards updates = do
  mod <- modifyModule id
  addTransNoState
    modifyModule
    ""
    ([
      EEq (EVar iContrState) (EInt 1),
      EEq (EVar iCommState) (EInt 1),
      EEq (EVar $ Ident $ sStatePrefix ++ (show $ number mod)) (EInt (-1))
    ] ++ guards)
    updates


---------------------
-- MONEY TRANSFERS --
---------------------

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
    modifyContract
    ""
    [EGe (EVar from) value, ELe (EAdd (EVar to) value) maxTo]
    [([(from, ESub (EVar from) value), (to, EAdd (EVar to) value)], [Alive])]

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

