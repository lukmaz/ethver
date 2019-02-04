module AuxEthEthver where

import Control.Monad.State
import qualified Data.Map.Strict as Map
import ErrM

import AbsEthver

-- TYPES --

type EthRes a = State EthWorld a

data EthWorld = EthWorld {
  contr :: String,
  scen :: String,
  ethTypes :: Map.Map Ident Type,
  ethFuns :: Map.Map Ident Function
}


-- INITIALIZATION --

emptyEthWorld :: EthWorld
emptyEthWorld = EthWorld {contr = "", scen = "",
  ethTypes = Map.empty,
  ethFuns = Map.empty
  }


-- WORLD MODIFICATION --

addContr :: String -> EthRes ()
addContr text = do
  world <- get
  put (world {contr = (contr world) ++ text})
  
addScen :: String -> EthRes ()
addScen text = do
  world <- get
  put (world {scen = (scen world) ++ text})
  
addEthVar :: Ident -> Type -> EthRes ()
addEthVar ident typ = do
  world <- get
  put (world {ethTypes = Map.insert ident typ (ethTypes world)})

addEthFun :: Function -> EthRes ()
addEthFun fun@(Fun funIdent args stms) = do
  mapM_ (\(Ar typ ident) -> addEthVar ident typ) args
  
  world <- get
  put (world {ethFuns = Map.insert funIdent fun (ethFuns world)})

-- AUX --

commaList :: (a -> EthRes ()) -> (String -> EthRes ()) -> [a] -> EthRes ()
commaList _ _ [] =
  return ()

commaList fun writeFun (h:t) = do
  fun h
  mapM_
    (\arg -> do
      writeFun ", "
      fun arg)
    t

ethFindType :: Ident -> EthRes (Maybe Type)
ethFindType ident = do
  world <- get
  return $ Map.lookup ident (ethTypes world)

ethFindFun :: Ident -> EthRes (Maybe Function)
ethFindFun ident = do
  world <- get
  return $ Map.lookup ident (ethFuns world)

