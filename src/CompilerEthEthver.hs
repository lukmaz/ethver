module CompilerEthEthver where

import Control.Monad.State

import AbsEthver
import AuxEthEthver
import AuxEthver
import ConstantsEthver
import ExpEthEthver

ethTree :: Program -> String
ethTree prog =
  let (a, world) = (runState (ethProgram prog)) emptyEthWorld
  in contr world
  

ethProgram :: Program -> EthRes ()
ethProgram (Prog _ constants contract communication scenarios) = do
  -- TODO: users?
  -- TODO: constants
  addContr solPragma
  ethContract constants contract
  addContr "\n"

-- Contract

-- TODO: UserDecl
ethContract :: [ConstantDecl] -> Contract -> EthRes ()
ethContract constants (Contr ident decls constr funs) = do
  addContr "contract "
  ethIdent ident
  addContr " {\n"
  isTimed <- ethConstants constants
  
  mapM_ ethDecl decls
  addContr "\n"
  
  ethConstructor constr isTimed

  if signaturesInContract decls funs 
    then addContr solSigDefaultFunctions
    else return ()

  mapM_ ethFun funs
  
  addContr "}"

ethConstants :: [ConstantDecl] -> EthRes Bool
ethConstants constants = do
  let 
    filtered = filter
      (\(Const ident val) -> ident == (Ident sTimeDelta))
      constants
  
  case filtered of
    [] -> return False
    [Const ident val] -> do
      addContr $ "uint " ++ sContractStart ++ ";\n"
      addContr $ "uint " ++ (unident ident) ++ " = "
      ethInteger val
      addContr ";\n"
      return True
      
ethConstructor :: Constructor -> Bool -> EthRes ()
ethConstructor (Constr stms) isTimed = do 
  addContr "constructor() public {\n"

  mapM_ ethStm stms

  if isTimed
    then addContr $ sContractStart ++ " = " ++ sNow ++ ";\n"
    else return ()

  addContr $ "}\n\n"

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

ethDecl (MapDec typ ident) = do
  addContr "mapping(address => "
  ethType typ
  addContr ") public "
  ethIdent ident
  addContr ";\n"

ethArg :: Arg -> EthRes ()
ethArg (Ar (TCUInt x) ident) = do
  addContr "uint8 "
  ethIdent ident
  addContr sCommitmentValSuffix
  addContr ", "
  addContr "string memory"
  addContr " "
  ethIdent ident
  addContr sCommitmentNonceSuffix

ethArg (Ar (TSig _) ident) = do
  addContr "uint8 "
  ethIdent ident
  addContr "_v, bytes32 "
  ethIdent ident
  addContr "_r, bytes32 "
  ethIdent ident
  addContr "_s"

ethArg (Ar typ ident) = do
  ethType typ
  addContr " "
  ethIdent ident

ethArgs :: [Arg] -> EthRes ()
ethArgs = commaList ethArg addContr

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

ethFun (FunL limit ident args stms) =
  ethFun (Fun ident args stms)

ethFun (FunVL limit ident args stms) =
  ethFun (Fun ident args stms)

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
