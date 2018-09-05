module CompilerEthEthver where

import Control.Monad.State

import AbsEthver
import AuxEthEthver


ethTree :: Program -> String
ethTree prog =
  let (a, world) = (runState (ethProgram prog)) emptyEthWorld
  in contr world
  

ethProgram :: Program -> EthRes ()
ethProgram (Prog _ _ contract communication scenarios) = do
  -- TODO: users?
  -- TODO: constants
  addContr "pragma solidity ^0.4.24;\n"
  ethContract contract
  addContr "\n"

-- Contract

-- TODO: UserDecl
ethContract :: Contract -> EthRes ()
ethContract (Contr ident decls funs) = do
  addContr "contract "
  ethIdent ident
  addContr " {\n"
  mapM_ ethDecl decls
  addContr "\n"
  mapM_ ethFun funs
  addContr "}"

-- TODO
ethCommunication :: Communication -> EthRes ()
ethCommunication _ = return ()

ethDecl :: Decl -> EthRes ()
ethDecl (Dec typ ident) = do
  ethType typ
  addContr " "
  ethIdent ident
  addContr ";\n"

ethDecl (DecInit typ ident value) = do
  ethType typ
  addContr " "
  ethIdent ident
  addContr " = "
  ethExp value
  addContr ";\n"

ethDecl (ArrDec typ ident size) = do
  ethType typ
  addContr "[] "
  ethIdent ident
  addContr ";\n"

ethArg :: Arg -> EthRes ()
ethArg (Ar typ ident) = do
  ethType typ
  addContr " "
  ethIdent ident

ethArgs :: [Arg] -> EthRes ()
ethArgs = commaList ethArg addContr

ethType :: Type -> EthRes ()
ethType (TUInt x) = do
  addContr "uint"

ethType (TAddr) = do
  addContr "address"

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
ethExp (EVar ident) = do
  ethIdent ident

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
ethExp (EMod e1 e2) = ethBinOp "%" e1 e2

ethExp (EArray ident index) = do
  ethIdent ident
  addContr "["
  ethExp index
  addContr "]"

ethExp (EValue) = addContr "msg.value"
ethExp (ESender) = addContr "msg.sender"

ethExp (EInt x) = ethInteger x
ethExp (ETrue) = addContr "true"
ethExp (EFalse) = addContr "false"

ethExp exp = do
  error $ (show exp) ++ ": ethExp not implemented for this expression"


-- ethExp aux

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
