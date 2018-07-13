module CompilerEthEthver where

import Control.Monad.State

import AbsEthver
import AuxEthEthver


ethTree :: Program -> (String, String)
ethTree prog =
  let (a, world) = (runState (ethProgram prog)) emptyEthWorld
  in (contr world, scen world)
  

ethProgram :: Program -> EthRes ()
ethProgram (Prog _ _ contract communication scenarios) = do
  -- TODO: users?
  -- TODO: constants
  ethContract contract
  ethCommunication communication
  mapM_ ethScenario scenarios


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

ethIdent :: Ident -> EthRes ()
ethIdent (Ident ident) = do
  addContr ident

ethFun :: Function -> EthRes ()
ethFun (Fun ident args stms) = do
  addContr "function "
  ethIdent ident
  addContr "("
  ethArgs args
  addContr ") {\n"
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


-- Stm

ethStm :: Stm -> EthRes ()

ethStm (SAss ident exp) = do
  ethIdent ident
  addContr " = "
  ethExp exp


ethStm (SReturn exp) = do
  addContr "return "
  ethExp exp
  addContr ";\n"

-- Ass


-- Exp

ethExp :: Exp -> EthRes ()
ethExp (EVar ident) = do
  ethIdent ident


-- Scenario

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

