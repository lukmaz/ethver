## The lexical structure of ETV 

### Identifiers 

Identifiers *Ident* are unquoted strings beginning with a letter,
followed by any combination of letters, digits, and the characters `_ '`
reserved words excluded.

### Literals 

String literals *String* have the form
`x`, where `x` is any sequence of any characters
except `"` unless preceded by `\`.

Integer literals *Integer* are nonempty sequences of digits.

### Reserved words and symbols 

The set of reserved words is the set of terminals appearing in the grammar. Those reserved words that consist of non-letter characters are called symbols, and they are treated in a different way from those that are similar to identifiers. The lexer follows rules familiar from languages like Haskell, C, and Java, including longest match and spacing conventions.

The reserved words used in ethver are the following:

|`address` |`bool` |`cash` |`cmt_uint`|
|---|---|---|---|
|`communication` |`constructor` |`contract` |`else`|
|`false` |`finney` |`function` |`hash`|
|`hashOf` |`if` |`mapping` |`nonce`|
|`payable` |`public` |`random` |`randomCmt`|
|`revealCmt` |`scenario` |`sendCommunication` |`sendTransaction`|
|`sign` |`signature` |`this` |`transfer`|
|`true` |`uint` |`user` |`value`|
|`valueOf` |`verCmt` |`verSig` |`wait`|
|`while` | ||

The symbols used in ethver are the following:

|; |= |{ |}|
|---|---|---|---|
|[ |] |( |=>|
|) |, |. ||
|&& |== |!= |<|
|<= |> |>= |+|
|- |* |/ |%|
|! |msg.value |msg.sender |:|

### Comments 

Single-line comments begin with //.Multiple-line comments are  enclosed with /* and */.

## The syntactic structure of ethver 

Non-terminals are enclosed between < and >. 
The symbols -> (production),  **|**  (union) 
and **eps** (empty rule) belong to the BNF notation. 
All other symbols are terminals.

|*Program* |-> |*[UserDecl]* *[ConstantDecl]* *Contract* *Communication* *[Scenario]*|
|*[UserDecl]* |-> |**eps**|
| |**|** |*UserDecl* `;` *[UserDecl]*|
|*[ConstantDecl]* |-> |**eps**|
| |**|** |*ConstantDecl* `;` *[ConstantDecl]*|
|*[Scenario]* |-> |**eps**|
| |**|** |*Scenario* *[Scenario]*|
|*UserDecl* |-> |`user` *String*|
|*ConstantDecl* |-> |*Ident* `=` *Integer*|
|*Contract* |-> |`contract` *Ident* `{` *[Decl]* *Constructor* *[Function]* `}`|
|*Decl* |-> |*Type* *Ident*|
| |**|** |*Type* *Ident* `=` *Exp*|
| |**|** |*Type* *Ident* `[` *Integer* `]`|
| |**|** |`mapping` `(` `address` `=>` *Type* `)` *Ident*|
|*[Decl]* |-> |**eps**|
| |**|** |*Decl* `;` *[Decl]*|
|*[Function]* |-> |**eps**|
| |**|** |*Function* *[Function]*|
|*Constructor* |-> |`constructor` `(` `)` `{` *[Stm]* `}`|
|*Communication* |-> |`communication` `{` *[Decl]* *[Function]* `}`|
|*Scenario* |-> |`scenario` *Ident* `{` *[Decl]* *[Stm]* `}`|
|*Function* |-> |`function` *Ident* `(` *[Arg]* `)` `public` `{` *[Stm]* `}`|
| |**|** |`function` *Ident* `(` *[Arg]* `)` `public` `payable` `{` *[Stm]* `}`|
|*Arg* |-> |*Type* *Ident*|
|*[Arg]* |-> |**eps**|
| |**|** |*Arg*|
| |**|** |*Arg* `,` *[Arg]*|
|*Stm* |-> |`{` *[Stm]* `}`|
| |**|** |*Ident* `=` *Exp* `;`|
| |**|** |*Ident* `[` *Exp* `]` `=` *Exp* `;`|
| |**|** |`if` `(` *Exp* `)` *Stm*|
| |**|** |`if` `(` *Exp* `)` *Stm* `else` *Stm*|
| |**|** |`while` `(` *Exp* `)` *Stm*|
| |**|** |*Exp* `.` `transfer` `(` *Exp* `)` `;`|
| |**|** |*Exp* `.` `sendTransaction` `(` *[CallArg]* `)` `;`|
| |**|** |*Exp* `.` `sendCommunication` `(` *[Exp]* `)` `;`|
| |**|** |*Exp* `.` `randomCmt` `(` `)` `;`|
| |**|** |*Exp* `.` `revealCmt` `(` `)` `;`|
| |**|** |`wait` `(` *Exp* `,` *Exp* `)` `;`|
|*[Stm]* |-> |**eps**|
| |**|** |*Stm* *[Stm]*|
|*[Exp]* |-> |**eps**|
| |**|** |*Exp*|
| |**|** |*Exp* `,` *[Exp]*|
|*Exp* |-> |*Exp* `||` *Exp1*|
| |**|** |*Exp1*|
|*Exp1* |-> |*Exp1* `&&` *Exp2*|
| |**|** |*Exp2*|
|*Exp2* |-> |*Exp2* `==` *Exp3*|
| |**|** |*Exp2* `!=` *Exp3*|
| |**|** |*Exp3*|
|*Exp3* |-> |*Exp3* `<` *Exp4*|
| |**|** |*Exp3* `<=` *Exp4*|
| |**|** |*Exp3* `>` *Exp4*|
| |**|** |*Exp3* `>=` *Exp4*|
| |**|** |*Exp4*|
|*Exp4* |-> |*Exp4* `+` *Exp5*|
| |**|** |*Exp4* `-` *Exp5*|
| |**|** |*Exp5*|
|*Exp5* |-> |*Exp5* `*` *Exp6*|
| |**|** |*Exp5* `/` *Exp6*|
| |**|** |*Exp5* `%` *Exp6*|
| |**|** |*Exp6*|
|*Exp6* |-> |`-` *Exp6*|
| |**|** |`!` *Exp6*|
| |**|** |`random` `(` *Exp6* `)`|
| |**|** |`sign` `(` *[Exp]* `)`|
| |**|** |`verSig` `(` *Exp* `,` *Exp* `,` `(` *[Exp]* `)` `)`|
| |**|** |`verCmt` `(` *Exp* `,` *Exp* `)`|
| |**|** |`finney` `(` *Integer* `)`|
| |**|** |*Exp7*|
|*Exp7* |-> |*Ident* `[` *Exp* `]`|
| |**|** |`valueOf` `(` *Exp7* `)`|
| |**|** |`hashOf` `(` *Exp7* `)`|
| |**|** |*Exp8*|
|*Exp8* |-> |`msg.value`|
| |**|** |`msg.sender`|
| |**|** |*Ident*|
| |**|** |*String*|
| |**|** |*Integer*|
| |**|** |`true`|
| |**|** |`false`|
| |**|** |`this`|
| |**|** |`(` *Exp* `)`|
|*[CallArg]* |-> |**eps**|
| |**|** |*CallArg*|
| |**|** |*CallArg* `,` *[CallArg]*|
|*CallArg* |-> |*Exp*|
| |**|** |`{` `value` `:` *Exp* `}`|
|*Type* |-> |`uint` `(` *Integer* `)`|
| |**|** |`cash` `(` *Integer* `)`|
| |**|** |`bool`|
| |**|** |`cmt_uint` `(` *Integer* `)`|
| |**|** |`signature` `(` *[Type]* `)`|
| |**|** |`address`|
| |**|** |`nonce`|
| |**|** |`hash`|
|*[Type]* |-> |**eps**|
| |**|** |*Type*|
| |**|** |*Type* `,` *[Type]*|

