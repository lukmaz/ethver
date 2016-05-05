module CompilerEthEthver where

import Control.Monad.State

import AbsEthver
import AuxEthEthver


ethTree :: Program -> (String, String)
ethTree prog =
  let (a, world) = (runState (ethProgram prog)) emptyEthWorld
  in (contr world, scen world)
  

ethProgram :: Program -> EthRes ()
ethProgram (Prog contract scenario) = do
  ethContract contract
  ethScenario scenario


-- Contract

ethContract :: Contract -> EthRes ()
ethContract (Contr ident decls funs) = do
  addContr "contract "
  ethIdent ident
  addContr " {\n"
  mapM_ ethDecl decls
  addContr "\n"
  mapM_ ethFun funs
  addContr "}"

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
ethStm (SExp exp) = do
  ethExp exp
  addContr ";\n"

ethStm (SReturn exp) = do
  addContr "return "
  ethExp exp
  addContr ";\n"


-- Exp

ethExp :: Exp -> EthRes ()
ethExp (EAss ident exp) = do
  ethIdent ident
  addContr " = "
  ethExp exp

ethExp (EVar ident) = do
  ethIdent ident


-- Scenario

ethScenario :: Scenario -> EthRes ()
ethScenario (Scen decls stms) = do
  mapM_ ethDecl decls
  mapM_ ethScStm stms

-- Stm

ethScStm :: Stm -> EthRes ()
ethScStm (SExp exp) = do
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

ethScExp (EAss ident exp) = do
  ethScIdent ident
  addScen " = "
  ethScExp exp
  addScen "\n"

ethScExp (ECall idents args) = do
  ethScIdents idents
  addScen "("
  commaList ethScCallArg addScen args
  addScen ")"


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

