module AuxEthver where

import AbsEthver

unident :: Ident -> String
unident (Ident ident) = ident

unvar :: Exp -> Ident
unvar (EVar ident) = ident

unvar exp = error $ show exp ++ "unvar can be applied only to EVar _"

signaturesInContract :: [Decl] -> [Function] -> Bool
signaturesInContract decls funs =
  (any signaturesInDecl decls) || (any signaturesInFunction funs)

signaturesInDecl :: Decl -> Bool
signaturesInDecl decl =
  case decl of
    (Dec t _) -> isSignatureType t
    (DecInit t _ _) -> isSignatureType t
    (ArrDec t _ _) -> isSignatureType t
    (MapDec t _) -> isSignatureType t

signaturesInFunction :: Function -> Bool
signaturesInFunction fun =
  case fun of
    Fun _ args _ -> checkArgs args 
    FunL _ _ args _ -> checkArgs args 
    FunV _ args _ -> checkArgs args 
    FunVL _ _ args _ -> checkArgs args 
    where
      checkArgs :: [Arg] -> Bool
      checkArgs args = any signaturesInArg args

signaturesInArg :: Arg -> Bool
signaturesInArg (Ar (TSig _) _) = True
signaturesInArg _ = False

isSignatureType :: Type -> Bool
isSignatureType t = case t of
  TSig _ -> True
  _ -> False

verSigArgsFromCond :: Exp -> [Exp]
verSigArgsFromCond cond = 
  case cond of
    EAnd a b -> verSigArgsFromCond a ++ verSigArgsFromCond b
    EOr a b -> verSigArgsFromCond a ++ verSigArgsFromCond b
    ENot a -> verSigArgsFromCond a
    EVerS _ _ args -> args
    _ -> []
