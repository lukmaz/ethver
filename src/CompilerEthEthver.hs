module CompilerEthEthver where

import Control.Monad.State

import AbsEthver
import AuxEthEthver
import AuxEthver
import ConstantsEthver
import ExpEthEthver
import ScenEthver

ethTree :: Program -> (String, String)
ethTree prog =
  let (a, world) = (runState (ethProgram prog)) emptyEthWorld
  in (contr world, scen world)
  

ethProgram :: Program -> EthRes ()
ethProgram (Prog _ constants contract communication scenarios) = do
  -- TODO: users?
  -- TODO: constants
  addContr solPragma
  ethContract constants contract

  ethCommunication communication
  
  scScenarios scenarios

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
  
  addContr "}\n"

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


ethDecl :: Decl -> EthRes ()
ethDecl (Dec typ ident) = do
  ethType typ
  addPayable typ
  addContr " public "
  ethIdent ident
  addContr ";\n"

ethDecl (DecInit typ ident value) = do
  ethType typ
  addPayable typ
  addContr " public "
  ethIdent ident
  addContr " = "
  ethExp value
  addContr ";\n"

ethDecl (ArrDec typ ident size) = do
  ethType typ
  addPayable typ
  addContr "["
  ethInteger size
  addContr "]"
  addContr " public "
  ethIdent ident
  addContr ";\n"

ethDecl (MapDec typ ident) = do
  addContr "mapping(address => "
  ethType typ
  addContr ")"
  addContr " public "
  ethIdent ident
  addContr ";\n"

addPayable :: Type -> EthRes ()
addPayable typ = do
  case typ of 
    TAddr -> addContr " payable"
    _ -> return ()
    
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


-------------------
-- Communication --
-------------------

ethCommunication :: Communication -> EthRes ()
ethCommunication (Comm decls funs) = do
  mapM_ scDecl decls
  mapM_ addEthFun funs

