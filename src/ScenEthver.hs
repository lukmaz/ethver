module ScenEthver where

import AbsEthver
import AuxEthver
import AuxEthEthver

--------------
-- Scenario --
--------------

scScenario :: Scenario -> EthRes ()
scScenario (Scen userName decls stms) = do
  mapM_ scDecl decls
  -- TODO: userName obsłużyć
  mapM_ scStm stms

---------
-- Stm --
---------

scStm :: Stm -> EthRes ()

scStm (SAss ident (ERand range)) = do
  scIdent ident
  addScen $ " =  web3.utils.randomHex(32) % " ++ show range

scStm (SAss ident exp) = do
  scIdent ident
  addScen " = "
  scExp exp
  addScen "\n"

scStm (SBlock stms) = do
  addScen "{\n"
  mapM_ scStm stms
  addScen "}\n"

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
  addScen ")"

-- TODO
scStm (SSendC (EVar funIdent) args) = do
  addScen $ "TODO: " ++ show funIdent ++ ".sendCommunication not implemented.\n"

scStm (SWait cond time) = do
  addScen $ "< WAIT UNTIL ("
  scExp cond
  addScen $ ") IS TRUE OR "
  scExp time
  addScen $ "TIME_DELTAs HAS PASSED >"

scStm (SRCmt (EVar (Ident varName))) = do
  typ <- ethFindType (Ident varName)
  case typ of
    Just (TCUInt range) -> do
      addScen $ varName ++ "_val = web3.utils.randomHex(32) % " ++ show range ++ "\n"
      addScen $ varName ++ "_nonce = web3.utils.randomHex(32)\n"
    _ -> 
      error $ "randomCommitment() can be called on TCUIint type only."

scStm stm = do
  error $ "scStm not implemented for: " ++ show stm

---------
-- Exp --
---------

scExp :: Exp -> EthRes ()

-- MATH
scExp (EAnd e1 e2) = scBinOp "&&" e1 e2
scExp (EOr e1 e2) = scBinOp "||" e1 e2
scExp (EEq e1 e2) = scBinOp "==" e1 e2
scExp (ENe e1 e2) = scBinOp "!=" e1 e2
scExp (ELt e1 e2) = scBinOp "<" e1 e2
scExp (ELe e1 e2) = scBinOp "<=" e1 e2
scExp (EGt e1 e2) = scBinOp ">" e1 e2
scExp (EGe e1 e2) = scBinOp ">=" e1 e2
scExp (EAdd e1 e2) = scBinOp "+" e1 e2
scExp (ESub e1 e2) = scBinOp "-" e1 e2
scExp (EMul e1 e2) = scBinOp "*" e1 e2
scExp (EDiv e1 e2) = scBinOp "/" e1 e2
scExp (EMod e1 e2) = scBinOp "%" e1 e2
scExp (ENeg e) = scUnOp "-" e
scExp (ENot e) = scUnOp "!" e

scExp (EVar ident) = do
  scIdent ident

scExp (EHashOf (EVar (Ident varName))) = do
  addScen $ "web3.utils.sha3(web3.utils.asciiToHex(" ++ varName ++ 
    "_val) + web3.utils.asciiToHex(" ++ varName ++ "_nonce).substring(2))"

scExp (EValOf (EVar (Ident varName))) = do
  addScen $ varName ++ "_val"

scExp (EVerS (EVar (Ident key)) (EVar (Ident sigName)) args) = do
  addScen $ "web3.eth.accounts.recover(_msg, " ++ 
    sigName ++ ".v, " ++ sigName ++ ".r" ++ sigName ++ ".s).toUpperCase() == " ++
    key ++ ".toUpperCase()"

scExp (EStr str) = do
  addScen "\""
  addScen str
  addScen "\""

scExp (EInt x) = do
  addScen (show x)

scExp ETrue = addScen "true"
scExp EFalse = addScen "false"

scExp EGetMy = addScen "< MY_ADDRESS >"

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
      addScen $ varName ++ ".substr(2)"
    Just (TUInt _) ->
      addScen $ "web3.utils.padLeft(" ++ varName ++ ", 2)"
    Just t ->
      error $ "Type " ++ show t ++ " not supported by concatExp."
    Nothing ->
      error $ "Cannot find ethType of " ++ varName

  
scCond :: Exp -> EthRes ()
scCond cond =
  case verSigArgsFromCond cond of
    [] -> return ()
    args -> do
      addScen "_concat = "
      concatExp $ head args
      mapM_
        (\arg -> do
          addScen " + "
          concatExp arg)
        (tail args)
      addScen "\n"

      addScen "_msg = \"msg\" + web3.utils.sha3(_concat)\n"
 
scUnOp op e = do
  addScen $ op ++ " "
  scExp e

scBinOp op e1 e2 = do
  scExp e1
  addScen $ " " ++ op ++ " "
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
scCallArg (AExp exp) = do
  scExp exp

scCallArg (ABra from value) = do
  addScen "{from: "
  scExp from
  addScen ", value: "
  scExp value
  addScen "}"


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
