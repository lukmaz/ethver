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

scStm (SAss ident exp) = do
  scIdent ident
  addScen " = "
  scExp exp
  addScen "\n"


scStm stm = do
  error $ "scStm not implemented for: " ++ show stm

---------
-- Exp --
---------

scExp :: Exp -> EthRes ()
scExp (EStr str) = do
  addScen "\""
  addScen str
  addScen "\""

scExp (EInt x) = do
  addScen (show x)

scExp (EVar ident) = do
  scIdent ident

scExp exp = do
  error $ "scExp not implemented for: " ++ show exp

---------
-- Aux --
---------

scDecl :: Decl -> EthRes ()

scDecl _ = return ()

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
