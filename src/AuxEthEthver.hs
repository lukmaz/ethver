module AuxEthEthver where

import Control.Monad.State
import ErrM


-- TYPES --

type EthRes a = State EthWorld a

data EthWorld = EthWorld {
  contr :: String,
  scen :: String,
  ver :: String
}


-- INITIALIZATION --

emptyEthWorld :: EthWorld
emptyEthWorld = EthWorld {contr = "", scen = "", ver = ""}


-- WORLD MODIFICATION --

addContr :: String -> EthRes ()
addContr text = do
  world <- get
  put (world {contr = (contr world) ++ text})
  
addScen :: String -> EthRes ()
addScen text = do
  world <- get
  put (world {scen = (scen world) ++ text})
  

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