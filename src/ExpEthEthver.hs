module ExpEthEthver where

import AbsEthver
import AuxEthver
import AuxEthEthver
import ConstantsEthver

ethType :: Type -> EthRes ()
ethType (TUInt x) = do
  addContr "uint8"

ethType (TCash x) = do
  addContr "uint"

ethType TBool = do
  addContr "bool"

ethType (TAddr) = do
  addContr "address"

ethType (THash) = do
  addContr "bytes32"

ethType t = error $ (show t) ++ ": not supported in ethType"

ethIdent :: Ident -> EthRes ()
ethIdent (Ident ident) = do
  addContr ident


---------
-- Stm --
---------

ethStm :: Stm -> EthRes ()

ethStm (SBlock stms) = do
  addContr "{\n"
  mapM_ ethStm stms
  addContr "}\n"

ethStm (SAss ident exp) = do
  ethIdent ident
  addContr " = "
  ethExp exp
  addContr ";\n"

ethStm (SArrAss ident index val) = do
  ethIdent ident
  addContr "["
  ethExp index
  addContr "] = "
  ethExp val
  addContr ";\n"

ethStm (SIf cond stm) = do
  ethCond cond
  addContr "if ("
  ethExp cond
  addContr ")\n"
  ethStm stm

ethStm (SIfElse cond stm1 stm2) = do
  ethCond cond
  addContr "if ("
  ethExp cond
  addContr ")\n"
  ethStm stm1
  addContr "else\n"
  ethStm stm2

ethStm (SSend receiver value) = do
  case receiver of
    (EStr "null") -> addContr "address(uint160(0))"
    _ -> ethExp receiver

  addContr ".transfer("
  ethExp value
  case value of
    EValue -> return ()
    EInt _ -> addContr " finney"
    _ -> return ()
  addContr ");\n"

ethStm stm = do
  error $ (show stm) ++ ": ethStm not implemented for this statement"

---------
-- Exp --
---------

ethExp :: Exp -> EthRes ()
-- MATH
ethExp e@(EAnd e1 e2) = ethBinOp "&&" e1 e2 $ rankExp e
ethExp e@(EOr e1 e2) = ethBinOp "||" e1 e2 $ rankExp e
ethExp e@(EEq e1 e2) = ethBinOp "==" e1 e2 $ rankExp e
ethExp e@(ENe e1 e2) = ethBinOp "!=" e1 e2 $ rankExp e
ethExp e@(ELt e1 e2) = ethBinOp "<" e1 e2 $ rankExp e
ethExp e@(ELe e1 e2) = ethBinOp "<=" e1 e2 $ rankExp e
ethExp e@(EGt e1 e2) = ethBinOp ">" e1 e2 $ rankExp e
ethExp e@(EGe e1 e2) = ethBinOp ">=" e1 e2 $ rankExp e
ethExp e@(EAdd e1 e2) = ethBinOp "+" e1 e2 $ rankExp e
ethExp e@(ESub e1 e2) = ethBinOp "-" e1 e2 $ rankExp e
ethExp e@(EMul e1 e2) = ethBinOp "*" e1 e2 $ rankExp e
ethExp e@(EDiv e1 e2) = ethBinOp "/" e1 e2 $ rankExp e
ethExp e@(EMod e1 e2) = ethBinOp "%" e1 e2 $ rankExp e
ethExp (ENeg e) = ethUnOp "-" e
ethExp (ENot e) = ethUnOp "!" e

ethExp (EArray ident index) = do
  ethIdent ident
  addContr "["
  ethExp index
  addContr "]"

ethExp (EVerC (EVar cmtVar) hash) = do
  let
    valVar = Ident $ unident cmtVar ++ sCommitmentValSuffix
    nonceVar = Ident $ unident cmtVar ++ sCommitmentNonceSuffix
  addContr "keccak256(abi.encodePacked(48 + "
  ethIdent valVar
  addContr ", "
  ethIdent nonceVar
  addContr ")) == "
  ethExp hash

ethExp (EValOf (EVar cmtVar)) = do
  ethIdent $ Ident $ unident cmtVar ++ sCommitmentValSuffix

ethExp (EVar ident) = do
  if ident == (Ident sTimeElapsed)
  then
      addContr $ "(" ++ sNow ++ " - " ++ sContractStart ++ ") / " ++ sTimeDelta
  else
      ethIdent ident

ethExp (EValue) = addContr "msg.value"
ethExp (ESender) = addContr "msg.sender"

ethExp (EInt x) = ethInteger x
ethExp (EFinney x) = do
  ethInteger x
  addContr " finney"

ethExp (ETrue) = addContr "true"
ethExp (EFalse) = addContr "false"

ethExp (EVerS key sigVar _) = do
  addContr "(ecrecover(_msgHash, "
  ethExp sigVar
  addContr "_v, "
  ethExp sigVar
  addContr "_r, "
  ethExp sigVar
  addContr "_s) == "
  ethExp key
  addContr ")"

ethExp exp = do
  error $ (show exp) ++ ": ethExp not implemented for this expression"

---------
-- Aux --
---------

ethCond :: Exp -> EthRes ()
ethCond cond =
  case verSigArgsFromCond cond of
    [] -> return ()
    args -> do
      addContr solCondPrefix
      ethExp $ head args
      mapM_
        (\arg -> do
          addContr ", "
          ethExp arg)
        (tail args)
      addContr solCondSuffix
    
ethUnOp :: String -> Exp -> EthRes ()
ethUnOp op e = do
  addContr $ op ++ "("
  ethExp e
  addContr ")"

ethBinOp :: String -> Exp -> Exp -> Integer -> EthRes ()
ethBinOp op e1 e2 rank = do
  if rankExp e1 < rank
    then do
      addContr "("
      ethExp e1
      addContr ")"
    else
      ethExp e1
  addContr $ " " ++ op ++ " "
  if rankExp e2 < rank
    then do
      addContr "("
      ethExp e2
      addContr ")"
    else
      ethExp e2

ethInteger :: Integer -> EthRes ()
ethInteger x =
  addContr (show x)


