module CompilerEthEthver where

import Control.Monad.State

import AbsEthver
import AuxEthEthver
import AuxEthver
import ConstantsEthver


ethTree :: Program -> String
ethTree prog =
  let (a, world) = (runState (ethProgram prog)) emptyEthWorld
  in contr world
  

ethProgram :: Program -> EthRes ()
ethProgram (Prog _ constants contract communication scenarios) = do
  -- TODO: users?
  -- TODO: constants
  addContr "pragma solidity ^0.4.24;\n"
  ethContract constants contract
  addContr "\n"

-- Contract

-- TODO: UserDecl
ethContract :: [ConstantDecl] -> Contract -> EthRes ()
ethContract constants (Contr ident decls funs) = do
  addContr "contract "
  ethIdent ident
  addContr " {\n"
  ethConstants constants
  mapM_ ethDecl decls
  addContr "\n"
  mapM_ ethFun funs
  addContr "}"

ethConstants :: [ConstantDecl] -> EthRes ()
ethConstants constants = do
  mapM_
    (
      \(Const ident val) -> 
        if ident == (Ident sTimeDelta) 
        then do
          addContr $ "uint " ++ sContractStart ++ ";\n"
          addContr $ "uint " ++ (unident ident) ++ " = "
          ethInteger val
          addContr ";\n"
          ethConstructor
        else return ()
    )
    constants

ethConstructor :: EthRes ()
ethConstructor = do
  addContr "constructor() public {\n"
  addContr $ sContractStart ++ " = " ++ sNow ++ ";\n"
  addContr $ "}\n"

-- TODO
ethCommunication :: Communication -> EthRes ()
ethCommunication _ = return ()

ethDecl :: Decl -> EthRes ()
ethDecl (Dec typ ident) = do
  ethType typ
  addContr " public "
  ethIdent ident
  addContr ";\n"

ethDecl (DecInit typ ident value) = do
  ethType typ
  addContr " public "
  ethIdent ident
  addContr " = "
  ethExp value
  addContr ";\n"

ethDecl (ArrDec typ ident size) = do
  ethType typ
  addContr "["
  ethInteger size
  addContr "] public "
  ethIdent ident
  addContr ";\n"

ethArg :: Arg -> EthRes ()
ethArg (Ar (TCUInt x) ident) = do
  addContr "uint8 "
  ethIdent ident
  addContr sCommitmentValSuffix
  addContr ", "
  addContr "string"
  addContr " "
  ethIdent ident
  addContr sCommitmentNonceSuffix

ethArg (Ar typ ident) = do
  ethType typ
  addContr " "
  ethIdent ident

ethArgs :: [Arg] -> EthRes ()
ethArgs = commaList ethArg addContr

ethType :: Type -> EthRes ()
ethType (TUInt x) = do
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

ethFun :: Function -> EthRes ()
ethFun (Fun ident args stms) = do
  addContr "function "
  ethIdent ident
  addContr "("
  ethArgs args
  addContr ") public {\n"
  mapM_ ethStm stms
  addContr "}\n"

ethFun (FunV ident args stms) = do
  addContr "function "
  ethIdent ident
  addContr "("
  ethArgs args
  addContr ") public payable {\n"
  mapM_ ethStm stms
  addContr "}\n"

ethFun (FunR ident args ret stms) = do
  addContr "function "
  ethIdent ident
  addContr "("
  ethArgs args
  addContr ") returns ("
  ethType ret
  addContr ") {\n"
  mapM_ ethStm stms
  addContr "}\n"

ethFun (FunL limit ident args stms) =
  ethFun (Fun ident args stms)

ethFun (FunVL limit ident args stms) =
  ethFun (Fun ident args stms)

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
  addContr "if ("
  ethExp cond
  addContr ")\n"
  ethStm stm

ethStm (SIfElse cond stm1 stm2) = do
  addContr "if ("
  ethExp cond
  addContr ")\n"
  ethStm stm1
  addContr "else\n"
  ethStm stm2

ethStm (SReturn exp) = do
  addContr "return "
  ethExp exp
  addContr ";\n"

ethStm (SSend receiver value) = do
  ethExp receiver
  addContr ".transfer("
  ethExp value
  addContr ");\n"

ethStm stm = do
  error $ (show stm) ++ ": ethStm not implemented for this statement"
-- Ass

---------
-- Exp --
---------

ethExp :: Exp -> EthRes ()
-- MATH
ethExp (EAnd e1 e2) = ethBinOp "&&" e1 e2
ethExp (EOr e1 e2) = ethBinOp "||" e1 e2
ethExp (EEq e1 e2) = ethBinOp "==" e1 e2
ethExp (ENe e1 e2) = ethBinOp "!=" e1 e2
ethExp (ELt e1 e2) = ethBinOp "<" e1 e2
ethExp (ELe e1 e2) = ethBinOp "<=" e1 e2
ethExp (EGt e1 e2) = ethBinOp ">" e1 e2
ethExp (EGe e1 e2) = ethBinOp ">=" e1 e2
ethExp (EAdd e1 e2) = ethBinOp "+" e1 e2
ethExp (ESub e1 e2) = ethBinOp "-" e1 e2
ethExp (EMul e1 e2) = ethBinOp "*" e1 e2
ethExp (EDiv e1 e2) = ethBinOp "/" e1 e2
ethExp (EMod e1 e2) = ethBinOpWithOnePar "%" e1 e2
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

ethExp exp = do
  error $ (show exp) ++ ": ethExp not implemented for this expression"


-- ethExp aux

ethUnOp op e = do
  addContr $ op ++ " "
  ethExp e

-- TODO: hack only for %
ethBinOpWithOnePar op e1 e2 = do
  addContr "("
  ethExp e1
  addContr $ ") " ++ op ++ " "
  ethExp e2

ethBinOp op e1 e2 = do
  ethExp e1
  addContr $ " " ++ op ++ " "
  ethExp e2

ethInteger :: Integer -> EthRes ()
ethInteger x =
  addContr (show x)

--------------
-- Scenario --
--------------

-- currently not used

ethScenario :: Scenario -> EthRes ()
ethScenario (Scen userName decls stms) = do
  mapM_ ethDecl decls
  -- TODO: userName obsłużyć
  mapM_ ethScStm stms

-- Stm

ethScStm :: Stm -> EthRes ()

ethScStm (SAss ident exp) = do
  ethScIdent ident
  addScen " = "
  ethScExp exp
  addScen "\n"


-- Exp

ethScExp :: Exp -> EthRes ()
ethScExp (EStr str) = do
  addScen "\""
  addScen str
  addScen "\""

ethScExp (EInt x) = do
  addScen (show x)

ethScExp (EVar ident) = do
  ethScIdent ident

{-
ethScExp (ECall ident args) = do
  ethScIdent ident
  addScen "("
  commaList ethScExp addScen args
  addScen ")"
-}

-- CallArg
ethScCallArg (AExp exp) = do
  ethScExp exp

ethScCallArg (ABra from value) = do
  addScen "{from: "
  ethScExp from
  addScen ", value: "
  ethScExp value
  addScen "}"


-- Ident

ethScIdents :: [Ident] -> EthRes ()
ethScIdents [h] =
  ethScIdent h

ethScIdents (h:t) = do
  ethScIdent h
  addScen "."
  ethScIdents t

ethScIdent :: Ident -> EthRes ()
ethScIdent (Ident ident) = do
  addScen ident
