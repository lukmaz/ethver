-- This file was previously used in both Contract and scenarios
-- Then it was used only in Scenarios and it's not optimized in DFS way
-- Finally it is used everywhere (back to the "OLD" version)

module ExpPrismEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import AbsEthver
import AuxEthver
import AuxPrismEthver
import AuxWorldPrismEthver
import CodePrismEthver
import ConstantsEthver
import WorldPrismEthver

---------
-- Stm --
---------

verStm :: ModifyModuleType -> Stm -> VerRes ()

verStm modifyModule (SAss ident exp) = 
  verFullAss modifyModule (SAss ident exp)

verStm modifyModule (SArrAss ident index exp) =
  verFullAss modifyModule (SArrAss ident index exp)

verStm modifyModule (SReturn exp) = do
  evalExp <- verExp modifyModule exp 
  world <- get 
  verStm modifyModule (SAss (head $ returnVar world) evalExp)

-- TODO: zrobić, żeby return wychodziło z wykonania bieżącej funkcji
verStm modifyModule (SIf cond ifBlock) = do
  evalCond <- verExp modifyModule cond
  mod <- modifyModule id
  let ifState = currState mod 
  addTransToNewState
    modifyModule
    ""  
    [evalCond]
    -- TODO: Alive?
    [([], [Alive])]
  verStm modifyModule ifBlock
  mod <- modifyModule id
  addCustomTrans
    modifyModule
    ""  
    ifState
    (currState mod)
    [negateExp evalCond]
    -- TODO: Alive?
    [([], [Alive])]

verStm modifyModule (SIfElse cond ifBlock elseBlock) = do
  evalCond <- verExp modifyModule cond
  mod <- modifyModule id
  let ifState = currState mod 
  addTransToNewState
    modifyModule
    ""  
    [evalCond]
    -- TODO: Alive?
    [([], [Alive])]
  verStm modifyModule ifBlock
  mod <- modifyModule id
  let endIfState = currState mod 
  addCustomTrans
    modifyModule
    ""  
    ifState
    (numStates mod + 1)
    [negateExp evalCond]
    -- TODO: Alive?
    [([], [Alive])]
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
    -- TODO: Alive?
    [([], [Alive])]
  _ <- modifyModule (setCurrState endIfState)
  return ()

verStm modifyModule (SWhile cond whileBlock) = do
  evalCond <- verExp modifyModule cond
  mod <- modifyModule id

  let
    breakState = (currState mod) + 1
    whileState = (currState mod) + 2

  addCustomTrans 
    modifyModule
    ""
    (currState mod)
    whileState
    []
    -- TODO: Alive?
    [([], [Alive])]

  modifyModule (setCurrState whileState)
  modifyModule (setNumStates whileState)

  modifyModule $ addBreakState breakState

  addTransToNewState
    modifyModule
    ""  
    [evalCond]
    -- TODO: Alive?
    [([], [Alive])]

  verStm modifyModule whileBlock
  mod <- modifyModule id

  -- go to begin of a loop
  addCustomTrans
    modifyModule
    ""
    (currState mod)
    whileState
    []
    -- TODO: Alive?
    [([], [Alive])]

  mod <- modifyModule id

  -- end of a loop
  addCustomTrans
    modifyModule
    ""  
    whileState
    (numStates mod + 1)
    [negateExp evalCond]
    -- TODO: Alive?
    [([], [Alive])]

  -- escape from breakState
  addCustomTrans
    modifyModule
    ""
    breakState
    (numStates mod + 1)
    []
    -- TODO: Alive?
    [([], [Alive])]

  mod <- modifyModule id
  let newState = numStates mod + 1
  modifyModule (setCurrState newState)
  modifyModule (setNumStates newState)

  modifyModule removeBreakState

  return ()

verStm modifyModule (SBreak) = do
  mod <- modifyModule id
  addCustomTrans
    modifyModule
    ""
    (currState mod)
    (head $ breakStates mod)
    []
    -- TODO: Alive?
    [([], [Alive])]

  mod <- modifyModule id
  let newState = numStates mod + 1
  modifyModule (setCurrState newState)
  modifyModule (setNumStates newState)
  return ()

verStm modifyModule (SBlock stms) = do
  mapM_ (verStm modifyModule) stms

verStm modifyModule (SSend receiverExp arg) = do
  val <- verExp modifyModule arg
  mod <- modifyModule id
  let actualSender = whichSender mod
  case receiverExp of
    ESender -> do
      world <- get
      case senderNumber world of
        Just number ->
          verStm 
            modifyModule 
            (SSend (EInt number) arg)
        _ ->
          error $ show (SSend receiverExp arg) ++ ": sendNumber not set"
    EStr receiverAddress -> do
      if receiverAddress == sNull
        then do
          burnMoney val
        else do
          receiverNumber <- getPlayerNumber receiverAddress
          let receiverBalance = Ident $ sBalancePrefix ++ (show receiverNumber) 
          transferFromContract receiverBalance val
    EInt receiverNumber -> do
      let receiverBalance = Ident $ sBalancePrefix ++ (show receiverNumber)
      transferFromContract receiverBalance val
    EVar receiverVar -> do
      verStm modifyModule $ SIfElse (EEq (EVar receiverVar) (EInt 0)) (SSend (EInt 0) arg) (SSend (EInt 1) arg)
    EArray arrName index -> do
      case index of
        ESender -> do
          world <- get
          case senderNumber world of
            Just number ->
              verStm 
                modifyModule 
                (SSend (EArray arrName (EInt number)) arg)
            _ -> 
              error $ show (SSend receiverExp arg) ++ ": sendNumber not set"
        EInt indexInt -> do
          verStm modifyModule $ SSend (EVar $ Ident $ (unident arrName) ++ "_" ++ (show indexInt)) arg
        _ -> error $ "(" ++ (show receiverExp) ++ ").send() not supported"

        

verStm modifyModule (SSendT funExp args) = do
  case funExp of
    EVar funIdent ->
      verSendTAux modifyModule funIdent args
    _ -> error "sendTransaction can be called only on an Ident object"

verStm modifyModule (SSendC funExp args) = do
  case funExp of
    EVar funIdent ->
      verSendCAux modifyModule funIdent args
    _ -> error "sendCommunication can be called only on an Ident object"

--------------------------------------
-- Commitments -----------------------
--------------------------------------
--
-- (TCUInt range) x
-- x = (range + 1) -> init
-- x = range -> is_committed
-- x = [0..(range-1)] -> is_revealed
--
--------------------------------------

-- RCmt not used directly (fused with calling a function(hash)
{- verStm modifyModule (SRCmt (EVar cmtVar)) = do
  typ <- findVarType cmtVar
  case typ of
    Just (TCUInt x) -> do
      verWithCommitment modifyModule cmtVar (\globalName -> SAss globalName (EInt x))
    _ -> 
      error $ unident cmtVar ++ ": randomCommitment can be called on cmt_uint object only"
-}


-- SOCmt not used directly; moved to ValueOf
{-verStm modifyModule (SOCmt (EVar cmtVar)) = do
  typ <- findVarType cmtVar
  case typ of
    Just (TCUInt range) -> do
      if (init $ unident cmtVar) == (sGlobalCommitments ++ "_")
      then do
        mod <- modifyModule id
        addTransToNewState 
          modifyModule 
          ""
          []
          -- TODO: Alive?
          (foldl
            (\acc x -> acc ++ [([(cmtVar, EInt x)], [Alive])])
            []
            [0..(range - 1)]
          )
      else do
        verWithCommitment modifyModule cmtVar (\globalName -> SOCmt $ EVar $ globalName)
-}


{- moze niepotrzebne? Jesli potrzebne, to jest szansa, ze dziala 
verStm modifyModule (SOCmt (EArray ident index)) = do
  case index of
    ESender -> do
      varExp <- toVar exp
      verStm modifyModule (SOCmt varExp)
    _ -> do
      let varName0 = (unident ident) ++ "_0"
      let varName1 = (unident ident) ++ "_1"
      typ <- findVarType (Ident varName0) -- TODO: sprawdzic, czy findVarType dziala na tablicach
      case typ of
        Just (TCUInt x) -> verSOCmtAux modifyModule varName0 varName1 index x
        _ -> error $ varName0 ++ "(0/1): openCommitment can be called on cmt_uint object only.\n"
          ++ "found type: " ++ (show typ)
      where
        verSOCmtAux modifyModule varName0 varName1 index x = 
          verStm modifyModule (SIfElse
            (EEq index (EInt 0))
            (SAss (Ident varName0) (ERand (EInt x)))
            (SAss (Ident varName1) (ERand (EInt x))))
-}

verStm modifyModule (SWait cond time) = do
  evalCond <- verExp modifyModule cond
  mod <- modifyModule id
  let playerNumber = number mod
  
  -- if blocked, allow to step the timelock
  addCustomTrans
    modifyModule
    sTimelockStep
    (currState mod)
    (currState mod)
    [ENot evalCond, ELt (EVar $ Ident sTimeElapsed) time]
    [([], [Alive])]

  -- if not blocked or timelock passed, go ahead
  addTransToNewState
    modifyModule
    ""
    [EOr evalCond $ EGe (EVar $ Ident sTimeElapsed) time]
    -- TODO: Alive?
    [([], [Alive])]
  
---------
-- Cmt --
---------

-- auxiliary function for translating between cmt var names and global cmt names
verWithCommitment :: ModifyModuleType -> Ident -> (Ident -> Stm) -> VerRes ()
verWithCommitment modifyModule cmtVar stmFromIdent = do
  let
    cmtId = EVar $ Ident $ unident cmtVar ++ sIdSuffix
    globalName0 = Ident $ sGlobalCommitments ++ "_0"
    globalName1 = Ident $ sGlobalCommitments ++ "_1"
  world <- get
  -- (OLD)
  {-case Map.lookup cmtVar $ commitmentsIds world of
    Just 0 ->
      verStm modifyModule (stmFromIdent globalName0)
    Just 1 ->
      verStm modifyModule (stmFromIdent globalName1)
    Nothing ->
      verStm modifyModule (SIfElse
        (EEq cmtId (EInt 0))
        (stmFromIdent globalName0)
        (stmFromIdent globalName1))
  -}
  verStm modifyModule (SIfElse
    (EEq cmtId (EInt 0))
    (stmFromIdent globalName0)
    (stmFromIdent globalName1))

---------
-- Ass --
---------

verFullAss :: ModifyModuleType -> Stm -> VerRes ()
-- (NEW) moved from SOCmt
verFullAss modifyModule (SAss varIdent (EValOf (EVar cmtVar))) = do
  -- cmtVar is in fact ignored. The player opens his own commitment and assigns the id of it to varIdent
  mod <- modifyModule id

  -- open the appropriate commitment
  addTransToNewState
    modifyModule
    (sOpenCommitment ++ (show $ number mod))
    []
    -- TODO: Alive?
    [([], [Alive])]


  -- assign player's commitment id

  (guards, updates) <- generateSimpleAss modifyModule (SAss varIdent (EInt $ number mod))
      
  addTransToNewState
    modifyModule
    ""
    guards
    -- TODO: Alive?
    [(updates, [Alive])]

  {- (OLD)
  mod <- modifyModule id
  let cmtId = Ident $ unident cmtVar ++ sIdSuffix
  typ <- findVarType $ Ident $ sGlobalCommitments ++ "_0"
  case typ of
    Just (TCUInt range) -> do
      let localVarIdent = Ident $ (moduleName mod) ++ sLocalSuffix ++ (show $ numLocals mod)
      addLocal modifyModule (TUInt range)
      addTransToNewState 
        modifyModule 
        ""
        []
        -- TODO: Alive?
        (foldl
          (\acc x -> acc ++ [([(localVarIdent, EInt x)], [Alive])])
          []
          [0..(range - 1)]
        )
      
      verWithCommitment modifyModule cmtVar (\globalName -> SAss globalName (EVar $ localVarIdent))
    Nothing -> do
      error $ (show cmtVar) ++ " not found by findVarType in verFullAss (SAss _ (EValOf _))"
    _ -> error $ (show typ) ++ " not supported by verFullAss (SAss _ (EValOf _))"
  -}

verFullAss modifyModule (SAss varIdent exp) = do
  case exp of
    ERandL (EInt _) ->
      addLazyRandom varIdent
    _ -> 
      return ()

  varTyp <- findVarType varIdent
  case varTyp of
    Just (TSig sigTypes) -> do
      case exp of
        ESign args -> do
          let keyIdent = Ident $ unident varIdent ++ sSigSuffix ++ sKeySuffix
          world <- get
          case senderNumber world of
            Just x -> verStm modifyModule (SAss keyIdent $ EInt x)
          argsVars <- mapM toVar args
          mapM_ (signOne varIdent) (zip (zip [0..] sigTypes) argsVars)
            where
              signOne :: Ident -> ((Integer, Type), Exp) -> VerRes ()
              signOne varIdent ((nr, sigTyp), (EVar rIdent)) = do
                let 
                  newIdent = Ident $ unident varIdent ++ sSigSuffix ++ show nr
                case sigTyp of
                  TCUInt _ -> do
                    verStm modifyModule (SAss newIdent $ EVar $ Ident $ unident rIdent ++ sIdSuffix)
                  TUInt x -> do
                    verStm modifyModule (SAss newIdent (EVar rIdent))
        _ -> error $ show exp ++ ": r-value for signature can only be a sign(...) function"

    
    _ -> do
      let 
        (newVarIdent, newExp) = 
          case varTyp of
            Just (TCUInt x) ->
              case exp of
                EVar rightIdent -> 
                  (Ident $ unident varIdent ++ sIdSuffix, EVar $ Ident $ unident rightIdent ++ sIdSuffix)
                ERand _ ->
                  (varIdent, exp)
                EInt _ ->
                  (varIdent, exp)
                _ -> 
                  error $ (show exp)
                    ++ ": RHS of assignment to cmt can only be a cmt variable or ERand (in openCommitment)"
                    ++ " or EInt (in randomCommitment)"
            _ -> (varIdent, exp)
        
      (guards, updates) <- generateSimpleAss modifyModule (SAss newVarIdent newExp)
      
      addTransToNewState
        modifyModule
        ""
        guards
        -- TODO: Alive?
        [(updates, [Alive])]

verFullAss modifyModule (SArrAss (Ident ident) index exp) = do
  case index of
    ESender -> do
      mod <- modifyModule id
      world <- get
      case senderNumber world of
        Just number ->
          verStm 
            modifyModule 
            (SAss (Ident $ ident ++ "_" ++ (show number)) exp)
        _ ->
          error $ show (SArrAss (Ident ident) index exp) ++ ": senderNumber not set"
    EVar v -> do
      var <- verExp modifyModule (EVar v)
      verStm 
        modifyModule 
        (SIf 
          (EEq var (EInt 0))
          (SAss (Ident $ ident ++ "_0") exp)
        )
      verStm
        modifyModule
        (SIf
          (EEq var (EInt 1))
          (SAss (Ident $ ident ++ "_1") exp)
        )
    EStr indexAddress -> do
      indexNumber <- getPlayerNumber indexAddress
      let indexVar = Ident $ ident ++ "_" ++ (show indexNumber)
      verStm modifyModule $ SAss indexVar exp
    EInt indexNumber -> do
      let indexVar = Ident $ ident ++ "_" ++ (show indexNumber)
      verStm modifyModule $ SAss indexVar exp

-- generateSimpleAss

-- returns simple updates [], not [[]]
generateSimpleAss :: ModifyModuleType -> Stm -> VerRes ([Exp], [(Ident, Exp)])
generateSimpleAss modifyModule (SAss ident exp) = do
  evalExp <- verExp modifyModule exp 
  typ <- findVarType ident
  minV <- minValue ident
  maxV <- maxTypeValue ident
  let guards = case typ of Just TBool -> []
                           Just _ -> [EGe evalExp (EInt minV), ELe evalExp (EInt maxV)]
  return (guards, [(ident, evalExp)])

generateSimpleAss modifyModule (SArrAss (Ident ident) index exp) = do
  case index of
    -- TODO: ESender (zmienić też verFullAss)
    EStr indexAddress -> do
      indexNumber <- getPlayerNumber indexAddress
      let indexVar = Ident $ ident ++ "_" ++ (show indexNumber)
      generateSimpleAss modifyModule $ SAss indexVar exp 
    EInt indexNumber -> do
      let indexVar = Ident $ ident ++ "_" ++ (show indexNumber)
      generateSimpleAss modifyModule $ SAss indexVar exp 


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
verExp modifyModule (ERand exp) = verRandom modifyModule exp
verExp modifyModule (ERandL exp) = verRandomLazy modifyModule exp

-- should be handled by sendT or so
--verExp modifyModule (EHashOf exp) = verValExp modifyModule (EHashOf exp)
verExp modifyModule EValue = verValExp modifyModule EValue
verExp modifyModule ESender = verValExp modifyModule ESender
verExp modifyModule (EInt x) = verValExp modifyModule (EInt x)
verExp modifyModule (EStr s) = verValExp modifyModule (EStr s)
verExp modifyModule (EFinney x) = verValExp modifyModule (EInt x)
verExp modifyModule ETrue = verValExp modifyModule ETrue
verExp modifyModule EFalse = verValExp modifyModule EFalse



-- TODO
-- temporary turned off

--verExp modifyModule (EVerS key signature vars) = verVerSig modifyModule key signature vars



verExp modifyModule (EVerC cmtVar hash) = verCmt modifyModule cmtVar hash

verExp _ exp = error $ (show exp) ++ ": not supported by verExp"

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
  return (EVar ident)
  -- (OLD) not needed anymore since each operation deals with TCUInt vars separately?
  {-
  typ <- findVarType ident
  case typ of
    Just (TCUInt x) -> do
      cmtVar <- commitmentVarName ident
      return $ EVar $ cmtVar
    _ ->
      return (EVar ident)
  -}

verValExp modifyModule (EArray (Ident ident) index) = do
  mod <- modifyModule id
  let localVarName = (moduleName mod) ++ sLocalSuffix ++ (show $ numLocals mod)
  -- TODO: liczba graczy = 2
  maybeType <- findVarType $ Ident $ ident ++ "_0"
  
  case index of
    ESender -> do
      world <- get
      case senderNumber world of
        Just x -> return $ EVar $ Ident $ ident ++ "_" ++ show x
    EVar v -> do
      case maybeType of
        Just typ -> do
          addLocal modifyModule typ
          var <- verExp modifyModule (EVar v)
          verStm 
            modifyModule 
            (SIf 
              (EEq var (EInt 0))
              (SAss (Ident $ localVarName) (EVar $ Ident $ ident ++ "_0"))
            )
          verStm
            modifyModule
            (SIf
              (EEq var (EInt 1))
              (SAss (Ident $ localVarName) (EVar $ Ident $ ident ++ "_1"))
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

-- Should not be called directly. EHashOf handled by verStm in all cases.
{-
verValExp modifyModule (EHashOf (EVar cmtVar)) = do
  world <- get
  -- (OLD)
  case Map.lookup cmtVar $ commitmentsIds world of
    Just x -> return $ EInt x
    Nothing -> error $ (show cmtVar) ++ 
      " not found in commitmentSIds. hashOf should not be called outside scenario"
-}

verValExp modifyModule EValue = do
  return EValue

-- czy na pewno tak można?
verValExp modifyModule ESender = do
  world <- get
  case senderNumber world of
    Just number ->
      return $ EInt $ number
    _ ->
      error $ "senderNumber not set"

verValExp modifyModule (EInt x) =
  return (EInt x)

-- strings only used as users names
verValExp modifyModule (EStr s) = do
  number <- getPlayerNumber s
  return (EInt number)

verValExp _ ETrue =
  return ETrue

verValExp _ EFalse =
  return EFalse


------------
-- Random --
------------
verRandom :: ModifyModuleType -> Exp -> VerRes Exp
verRandom modifyModule (EInt range) = do
  mod <- modifyModule id
  let localVarName = (moduleName mod) ++ sLocalSuffix ++ (show $ numLocals mod)
  addLocal modifyModule (TUInt range)
  addTransToNewState 
    modifyModule 
    ""
    []
    -- TODO: Alive?
    (foldl
      (\acc x -> acc ++ [([(Ident localVarName, EInt x)], [Alive])])
      []
      [0..(range - 1)]
    )
  return (EVar $ Ident localVarName)

verRandomLazy :: ModifyModuleType -> Exp -> VerRes Exp
verRandomLazy modifyModule (EInt range) = do
  return $ EInt range

----------------
-- Signatures --
----------------

-- TODO --
-- TEMPORARY TURNED OFF
-- SINCE IT IS NOT NEEDED IN RPS
--




{-
verVerSig :: ModifyModuleType -> Exp -> Exp -> [Exp] -> VerRes Exp
verVerSig modifyModule key (EVar signatureVar) varsOrArrs = do
  sigMaybeTyp <- findVarType signatureVar
  vars <- mapM toVar varsOrArrs
  case sigMaybeTyp of
    Just (TSig sigTypes) -> do
      world <- get
      let
        sigKey = Ident $ unident signatureVar ++ sSigSuffix ++ sKeySuffix
        f :: Ident -> Map.Map Ident Integer -> Exp -> ((Integer, Type), Exp) -> Exp
        f signatureVar commitmentsIds acc ((nr, sigType), var) = 
          case sigType of
            TCUInt x ->
              let 
                sigId = Ident $ unident signatureVar ++ sSigSuffix ++ show nr
                varId = Ident $ (unident $ unvar var) ++ sIdSuffix
              in
                EAnd acc (EEq (EVar sigId) (EVar varId))
            TUInt x ->
              let
                sigId = Ident $ unident signatureVar ++ sSigSuffix ++ show nr
              in
                EAnd acc (EEq (EVar sigId) var)
                
      return $ foldl (f signatureVar (commitmentsIds world)) (EEq (EVar sigKey) key) (zip (zip [0..] sigTypes) vars)
    Nothing -> error $ show signatureVar ++ ": not found by findVarType"

verVerSig modifyModule key (EArray arrIdent index) varsOrArrs = do
  case index of
    EInt x ->
      verVerSig modifyModule key (EVar $ Ident $ unident arrIdent ++ "_" ++ (show x)) varsOrArrs
    ESender -> do
      world <- get
      case senderNumber world of
        Just nr ->
          verVerSig modifyModule key (EVar $ Ident $ unident arrIdent ++ "_" ++ (show $ nr)) varsOrArrs
        _ ->
          error $ "senderNumber world not defined"
    _ -> error $ show index ++ ": not supported index for arrays"
-}













verCmt :: ModifyModuleType -> Exp -> Exp -> VerRes Exp
verCmt modifyModule cmtVar hash = do 
  evalHash <- verExp modifyModule hash
  world <- get
  let
    cmtId = EVar $ Ident $ unident (unvar cmtVar) ++ sIdSuffix
  return $ EEq cmtId evalHash

  {-  OLD, to delete:
    cmtName0 = Ident $ sGlobalCommitments ++ "_0"
    cmtName1 = Ident $ sGlobalCommitments ++ "_1"
    r0 = EEq (EVar cmtName0) evalHash
    r1 = EEq (EVar cmtName1) evalHash
  return $ EOr
    (EAnd (EEq cmtId (EInt 0)) r0)
    (EAnd (EEq cmtId (EInt 1)) r1)
  -}

-----------------------------
-- Call auxilary functions --
-----------------------------
-- TODO: nie uzywam
{-
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
  let retVarIdent = Ident ((unident name) ++ sReturnValueSuffix)
  addReturnVar retVarIdent
  mapM_ (verStm modifyModule) stms
  removeReturnVar
  return (EVar retVarIdent)
--TODO: to jest przepisane z verScFunSendT
-}
-------------
-- ScSendT --
-------------
-- (OLD) Assumption: If there is a cmt argument, the function  must be called when it's in "committed" state
-- and it automatically opens it.
-- (NEW) opening moved to ValueOf
verSendTAux :: ModifyModuleType -> Ident -> [CallArg] -> VerRes ()
verSendTAux modifyModule funName argsVals = do
  world <- get
  mod <- modifyModule id
  case Map.lookup funName (funs world) of
    Just fun -> do
      let argNames = getArgNames fun
      -- TODO: olewamy "from", bo sender jest wiadomy ze scenariusza
      let expArgsVals = map (\(AExp exp) -> exp) (init argsVals)
      evalArgsVals <- mapM (evalArg modifyModule) expArgsVals
     
      --evalArgsNames <- mapM (evalArgName modifyModule) argNames
      
      let (value, guards1) = case (last argsVals) of (ABra _ value) -> (value, [])
       
      -- TODO: ta linijka chyba jest nie potrzebna w function_without_value
      let updates0 = [[(Ident $ (unident funName) ++ sValueSuffix ++ (show $ number mod), value)]]
      let addAssignment acc (argName, argVal) = acc ++ createAssignments (number mod) funName argName argVal
      --TODO: Alive?
      let updates1Root = foldl addAssignment (head updates0) $ zip argNames evalArgsVals
      
      -- (OLD) simplification: only one commitment/player allowed so open this commitment
      -- (NEW) moved to ValueOf
      -- let cmtVar = Ident $ sGlobalCommitments ++ "_" ++ (show $ number mod)
      -- typ <- findVarType cmtVar
      -- let updates2 = modifyUpdatesIfCmtInArgs cmtVar typ fun updates1Root
      let updates2 = [(updates1Root, [Alive])]
      
      addTransToNewState 
        modifyModule 
        (sBroadcastPrefix ++ (unident funName) ++ (show $ number mod)) 
        guards1
        updates2

      addTransToNewState
        modifyModule
        ""
        [ 
          EEq 
            (EVar (Ident (unident funName ++ sStatusSuffix ++ (show $ number mod)))) 
            (EVar iTExecuted)
        ]
        --TODO: Alive?
        [([], [Alive])]

-----------
-- SendC --
-----------

verSendCAux :: ModifyModuleType -> Ident -> [Exp] -> VerRes ()
verSendCAux modifyModule funName expArgsVals = do
  world <- get
  mod <- modifyModule id
  case Map.lookup funName (funs world) of
    Just fun -> do
      let argNames = getArgNames fun
      evalArgsVals <- mapM (evalArg modifyModule) expArgsVals

      --evalArgsNames <- mapM (evalArgName modifyModule) argNames
      let addAssignment acc (argName, argVal) = acc ++ createAssignments (number mod) funName argName argVal
      --TODO: Alive?
      let updates1Root = foldl addAssignment [] $ zip argNames evalArgsVals
      
      -- (OLD) simplification: only one commitment/player allowed so open this commitment
      -- (NEW) moved to ValueOf
      -- let cmtVar = Ident $ sGlobalCommitments ++ "_" ++ (show $ number mod)
      -- typ <- findVarType cmtVar
      -- let updates2 = modifyUpdatesIfCmtInArgs cmtVar typ fun updates1Root
      let updates2 = [(updates1Root, [Alive])]

      addTransToNewState
        modifyModule
        ""
        []
        updates2

      addTransToNewState
        modifyModule
        (sCommunicatePrefix ++ (unident funName) ++ (show $ number mod))
        []
        --TODO: Alive?
        [([], [Alive])]
    _ -> error $ "Function " ++ (unident funName) ++ " not found in (funs world)"

-- TODO: adds function name in prefix of a variable name
createAssignments :: Integer -> Ident -> Arg -> Exp -> [(Ident, Exp)]
createAssignments playerNumber funName (Ar (TCUInt _) varName) (EInt x) =
  [(Ident $ unident varName ++ (show playerNumber) ++ sIdSuffix, EInt x)]

createAssignments playerNumber funName (Ar (TCUInt _) varName) (EVar argVal) =
  [(Ident $ unident varName ++ (show playerNumber) ++ sIdSuffix, EVar $ Ident $ unident argVal ++ sIdSuffix)]

createAssignments playerNumber funName (Ar (TCUInt x) varName) (EArray argVal index) =
  case index of 
    EInt x ->
      createAssignments playerNumber funName (Ar (TCUInt x) varName) (EVar $ Ident $ unident argVal ++ "_" ++ show x)
    _ ->
      error $ (show index) ++ ": array index type not supported"

createAssignments playerNumber funName (Ar _ varName) exp =
  [(createScenarioArgumentName "" funName varName playerNumber, exp)]

evalArg :: ModifyModuleType -> Exp -> VerRes Exp
evalArg modifyModule exp = 
  do
    case exp of
      EHashOf (EVar varIdent) -> return $ EVar varIdent
      EVar varIdent -> do
        typ <- findVarType varIdent
        case typ of
          Just (TCUInt _) -> return $ EVar varIdent
          _ -> return exp
      _ -> return exp

  {- (OLD)
  where
    idOfCmt :: Ident -> VerRes Exp
    idOfCmt varIdent = do
      world <- get
      case Map.lookup varIdent $ commitmentsIds world of
        Just x -> return $ EInt x
        _ -> error $ show varIdent ++ " not found in commitmentsIds"
  -}

{-
evalArgName :: ModifyModuleType -> Arg -> VerRes Arg
evalArgName modifyModule (Ar (TCUInt x) varName) = 
  return $ Ar (TCUInt x) (Ident $ unident varName ++ sIdSuffix)

evalArgName modifyModule arg = return arg
-}  
