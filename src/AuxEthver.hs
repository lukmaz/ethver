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
    FunV _ args _ -> checkArgs args 
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

rankExp :: Exp -> Integer
rankExp exp = 
  case exp of
    EOr _ _     -> 0
    EAnd _ _    -> 1
    EEq _ _     -> 2 
    ENe _ _     -> 2  
    ELt _ _     -> 3  
    ELe _ _     -> 3  
    EGt _ _     -> 3  
    EGe _ _     -> 3  
    EAdd _ _    -> 4 
    ESub _ _    -> 4 
    EMul _ _    -> 5 
    EDiv _ _    -> 5 
    EMod _ _    -> 5 
    ENeg _      -> 6 
    ENot _      -> 6 
    EArray _ _  -> 7
    ERand _     -> 7
    ESign _     -> 7
    EVerS _ _ _ -> 7
    EVerC _ _   -> 7
    EValOf _    -> 7
    EHashOf _   -> 7
    EVar _      -> 7
    EValue      -> 7
    ESender     -> 7
    EStr _      -> 7
    EInt _      -> 7
    EFinney _   -> 7
    ETrue       -> 7
    EFalse      -> 7
    EGetMy      -> 7
