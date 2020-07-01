module ScenEthver where

import AbsEthver
import AuxEthver
import AuxEthEthver

--------------
-- Scenario --
--------------

scScenarios :: [Scenario] -> EthRes ()
scScenarios [scenario0, scenario1] = do
  addScen $ "" ++
    "---------------------------\n" ++
    "-- First player scenario --\n" ++
    "---------------------------\n\n"

  scScenario scenario0

  addScen $ "" ++
    "----------------------------\n" ++
    "-- Second player scenario --\n" ++
    "----------------------------\n\n"

  scScenario scenario1

scScenario :: Scenario -> EthRes ()
scScenario (Scen userName decls stms) = do
  mapM_ scDecl decls
  mapM_ scStm stms

---------
-- Stm --
---------

scStm :: Stm -> EthRes ()

scStm (SAss ident (ERand range)) = do
  scIdent ident
  addScen $ " =  web3.utils.randomHex(6) % "
  scExp range
  addScen "\n\n"

scStm (SAss sigIdent (ESign args)) = do
  addScen "_sign_concat = "
  concatExp $ head args
  mapM_
    (\arg -> do
      addScen " + "
      concatExp arg)
    (tail args)
  addScen "\n\n"

  addScen "_sign_msg = \"msg\" + web3.utils.sha3(_sign_concat)\n\n"

  scIdent sigIdent
  addScen $ " = web3.eth.accounts.sign(_sign_msg, <MY PRIVATE KEY>)\n\n"

scStm (SAss ident exp) = do
  scIdent ident
  addScen " = "
  scExp exp
  addScen "\n\n"

scStm (SBlock stms) = do
  addScen "{\n"
  mapM_ scStm stms
  addScen "}\n\n"

scStm (SIf cond stm) = do
  scCond cond
  addScen "if ("
  scExp cond
  addScen ")\n"
  scStm stm

scStm (SIfElse cond stm1 stm2) = do
  scCond cond
  addScen "if ("
  scExp cond
  addScen ")\n"
  scStm stm1
  addScen "else\n"
  scStm stm2

scStm (SSendT (EVar funIdent) callArgs) = do
  scIdent funIdent
  addScen ".sendTransaction("
  scCallArg $ head callArgs
  mapM_ 
    (\arg -> do
      addScen ", "
      scCallArg arg)
    (tail callArgs)
  addScen ")\n\n"

scStm (SSendC (EVar funIdent) args) = do
  fun <- ethFindFun funIdent
  case fun of
    Just (Fun _ funArgs stms) -> do
      mapM_ scAssignArg (zip funArgs args)
      mapM_ scStm stms


scStm (SWait cond time) = do
  addScen $ "<WAIT UNTIL ("
  scExp cond
  addScen $ ") IS TRUE OR "
  scExp time
  addScen $ " TIME_DELTA(s) HAS PASSED>\n\n"

scStm (SRCmt (EVar (Ident varName))) = do
  typ <- ethFindType (Ident varName)
  case typ of
    Just (TCUInt range) -> do
      addScen $ varName ++ "_val = web3.utils.randomHex(6) % " ++ show range ++ "\n"
      addScen $ varName ++ "_nonce = web3.utils.randomHex(32)\n\n"
    _ -> 
      error $ "randomCommitment() can be called on TCUIint type only."

scStm (SRev _) =
  return ()

scStm stm = do
  error $ "scStm not implemented for: " ++ show stm

---------
-- Exp --
---------

scExp :: Exp -> EthRes ()

-- MATH
scExp e@(EAnd e1 e2) = scBinOp "&&" e1 e2 $ rankExp e
scExp e@(EOr e1 e2) = scBinOp "||" e1 e2 $ rankExp e
scExp e@(EEq e1 e2) = scBinOp "==" e1 e2 $ rankExp e
scExp e@(ENe e1 e2) = scBinOp "!=" e1 e2 $ rankExp e
scExp e@(ELt e1 e2) = scBinOp "<" e1 e2 $ rankExp e
scExp e@(ELe e1 e2) = scBinOp "<=" e1 e2 $ rankExp e
scExp e@(EGt e1 e2) = scBinOp ">" e1 e2 $ rankExp e
scExp e@(EGe e1 e2) = scBinOp ">=" e1 e2 $ rankExp e
scExp e@(EAdd e1 e2) = scBinOp "+" e1 e2 $ rankExp e
scExp e@(ESub e1 e2) = scBinOp "-" e1 e2 $ rankExp e
scExp e@(EMul e1 e2) = scBinOp "*" e1 e2 $ rankExp e
scExp e@(EDiv e1 e2) = scBinOp "/" e1 e2 $ rankExp e
scExp e@(EMod e1 e2) = scBinOp "%" e1 e2 $ rankExp e
scExp (ENeg e) = scUnOp "-" e
scExp (ENot e) = scUnOp "!" e

scExp (EVar ident) = do
  scIdent ident

scExp (EArray ident index) = do
  scIdent ident
  addScen "["
  scExp index
  addScen "]"

scExp (EHashOf (EVar (Ident varName))) = do
  addScen $ "web3.utils.sha3(web3.utils.toHex(" ++ varName ++ 
    "_val).substr(2) + web3.utils.toHex(" ++ varName ++ "_nonce))"

scExp (EValOf (EVar (Ident varName))) = do
  addScen $ varName ++ "_val"

scExp (EVerS (EVar (Ident key)) (EVar (Ident sigName)) args) = do
  addScen $ "web3.eth.accounts.recover(_ver_msg, " ++ 
    sigName ++ ".v, " ++ sigName ++ ".r, " ++ sigName ++ ".s).toLowerCase() == " ++
    key ++ ".toLowerCase()"

scExp (EStr str) = do
  addScen "\""
  addScen str
  addScen "\""

scExp (EInt x) = do
  addScen (show x)

scExp ETrue = addScen "true"
scExp EFalse = addScen "false"

scExp EGetMy = addScen "<MY_ADDRESS>"
scExp ESender = addScen "<MY_ADDRESS>"

scExp exp = do
  error $ "scExp not implemented for: " ++ show exp

---------
-- Aux --
---------

concatExp :: Exp -> EthRes ()

concatExp (EHashOf exp) =
  scExp (EHashOf exp)

concatExp (EVar (Ident varName)) = do
  typ <- ethFindType (Ident varName)
  case typ of
    Just TAddr ->
      addScen $ varName ++ ".toLowerCase().substr(2)"
    Just (TUInt _) ->
      addScen $ "web3.utils.padLeft(web3.utils.toHex(" ++ varName ++ ").substr(2), 2)"
    Just THash ->
      addScen varName
    Just t ->
      error $ "Type " ++ show t ++ " not supported by concatExp."
    Nothing ->
      error $ "Cannot find ethType of " ++ varName

  
scCond :: Exp -> EthRes ()
scCond cond =
  case verSigArgsFromCond cond of
    [] -> return ()
    args -> do
      addScen "_ver_concat = "
      concatExp $ head args
      mapM_
        (\arg -> do
          addScen " + "
          concatExp arg)
        (tail args)
      addScen "\n\n"

      addScen "_ver_msg = \"msg\" + web3.utils.sha3(_ver_concat)\n\n"

scUnOp :: String -> Exp -> EthRes ()
scUnOp op e = do
  addScen $ op ++ "("
  scExp e
  addScen ")"

scBinOp :: String -> Exp -> Exp -> Integer -> EthRes ()
scBinOp op e1 e2 rank = do
  if rankExp e1 < rank
    then do
      addScen "("
      scExp e1
      addScen ")"
    else
      scExp e1
  addScen $ " " ++ op ++ " "
  if rankExp e2 < rank
    then do
      addScen "("
      scExp e2
      addScen ")"
    else
      scExp e2

scDecl :: Decl -> EthRes ()

scDecl (Dec typ ident) = 
  addEthVar ident typ

scDecl (DecInit typ ident value) = do 
  scDecl (Dec typ ident)
  scStm (SAss ident value)

scDecl x = 
  error $ "scDecl not implemented for " ++ show x

-- CallArg
scCallArg :: CallArg -> EthRes ()

scCallArg (AExp exp) =
  scCallArgExp exp

scCallArg (ABra value) = do
  addScen "{from: "
  scExp EGetMy
  addScen ", value: "
  scExp value
  addScen "}"

scCallArgExp :: Exp -> EthRes ()

scCallArgExp (EVar varIdent@(Ident varName)) = do
  typ <- ethFindType varIdent
  case typ of
    Just (TCUInt _) ->
      addScen $ varName ++ "_val, " ++ varName ++ "_nonce"
    Just (TSig _) -> do
      addScen $ varName ++ ".v, " ++ varName ++ ".r, " ++ varName ++ ".s"
    _ ->
      scExp $ EVar varIdent

scCallArgExp (EHashOf (EVar varIdent)) = do
  scExp (EHashOf (EVar varIdent))

scCallArgExp (EInt x) = do
  scExp $ EInt x

-- Ident

scIdents :: [Ident] -> EthRes ()
scIdents [h] =
  scIdent h

scIdents (h:t) = do
  scIdent h
  addScen "."
  scIdents t

scIdent :: Ident -> EthRes ()
scIdent (Ident ident) = do
  addScen ident

scAssignArg :: (Arg, Exp) -> EthRes ()
scAssignArg ((Ar typ ident), arg) = do
  case typ of
    _ -> do
      scStm (SAss ident arg)
