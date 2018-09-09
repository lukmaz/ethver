module AuxEthver where

import AbsEthver

unident :: Ident -> String
unident (Ident ident) = ident

unvar :: Exp -> Ident
unvar (EVar ident) = ident

unvar exp = error $ show exp ++ "unvar can be applied only to EVar _"

