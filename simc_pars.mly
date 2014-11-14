%{
open Simc
%}

%token AMP
%token ADD SUB MUL DIV MOD LEQ LE GEQ GR EQ NEQ

%token EOF LPAR RPAR LBRAC RBRAC LCURL RCURL DEF COLON SCOLON COMMA DOT INT VOID
%token IF ELSE RETURN GOTO CONTINUE BREAK WHILE FOR SWITCH CASE DEFAULT STRUCT DO
%token <int>    VAL
%token <string> ID
%token <string> STRING

%start decls
%type <Simc.expr>       exp
%type <Simc.lval>       lval
%type <Simc.typ>        typ
%type <Simc.stmt>       stmt
%type <Simc.decl list>  decls

%right THEN ELSE
%nonassoc LOW AMP DEF
%nonassoc LEQ LE GEQ GR EQ NEQ
%left ADD SUB
%left MUL DIV MOD
%nonassoc DOT LBRAC LPAR

%%

lval: ID                    { Var $1 }
    | MUL s_exp             { Deref $2 }
    | lval DOT ID           { Field ($1,$3) }
    | lval LBRAC exp RBRAC  { Index ($1,$3) }
    ;

f_args_:                    { [] }
       | COMMA exp f_args_  { $2::$3 }
       ;

f_args:              { [] }
      | exp f_args_  { $1::$2 }
      ;

ints:            { [] }
    | VAL ints_  { $1::$2 }
    ;
ints_:                  { [] }
     | COMMA VAL ints_  { $2::$3 }
     ;

s_exp: VAL                     { Val $1 }
     | STRING                  { Val 0 } (* strings are treated as 0 *)
     | AMP lval                { Addr $2 }
     | lval     %prec LOW      { Lval $1 }
     | s_exp LPAR f_args RPAR  { App ($1,$3) }
     | LPAR exp RPAR           { $2 }
     ;

exp: s_exp        { $1 }
   | exp ADD exp  { Binop ($1,Add,$3) }
   | exp SUB exp  { Binop ($1,Sub,$3) }
   | exp MUL exp  { Binop ($1,Mul,$3) }
   | exp DIV exp  { Binop ($1,Div,$3) }
   | exp MOD exp  { Binop ($1,Mod,$3) }
   | exp LEQ exp  { Binop ($1,Leq,$3) }
   | exp LE  exp  { Binop ($1,Le ,$3) }
   | exp GEQ exp  { Binop ($1,Geq,$3) }
   | exp GR  exp  { Binop ($1,Gr ,$3) }
   | exp EQ  exp  { Binop ($1,Eq ,$3) }
   | exp NEQ exp  { Binop ($1,Neq,$3) }
   | exp DEF exp  { Binop ($1,Asn,$3) }
   | exp ADD DEF exp  { Binop ($1,Asn,Binop ($1,Add,$4)) }
   | exp SUB DEF exp  { Binop ($1,Asn,Binop ($1,Sub,$4)) }
   | exp MUL DEF exp  { Binop ($1,Asn,Binop ($1,Mul,$4)) }
   | exp DIV DEF exp  { Binop ($1,Asn,Binop ($1,Div,$4)) }
   | exp ADD ADD { Binop ($1,Asn,Binop ($1,Add,Val 1)) }
   | exp SUB SUB { Binop ($1,Asn,Binop ($1,Sub,Val 1)) }
   ;

typ: INT        { Int }
   | VOID       { Void }
   | STRUCT ID  { Struct $2 }
   | typ MUL    { Ptr $1 }
   ;

init: exp              { $1 }
   | LCURL ints RCURL  { ArrInit $2 }
   ;

vdecl: typ ID              { ($1,$2) }
     | typ ID LBRAC RBRAC  { Arr $1, $2 }
     ;

vdecls:                      { [] }
      | vdecl SCOLON vdecls  { $1::$3 }
      ;

decl: STRUCT ID LCURL vdecls RCURL             { StructDecl ($2,$4) }
    | vdecl SCOLON                             { Global (fst $1, snd $1, None) }
    | vdecl DEF init SCOLON                    { Global (fst $1, snd $1, Some $3) }
    | typ ID LPAR args RPAR LCURL stmts RCURL  { Function ($1,$2,$4,$7) }
    ;

args:              { [] }
    | vdecl args_  { $1::$2 }
    ;

args_:                    {[]}
     | COMMA vdecl args_  { $2::$3 }
     ;

decls: decl decls  { $1::$2 }
     | EOF         { [] }
     ;

stmt: SCOLON                                        { Nop }
    | exp SCOLON                                    { Expr $1 }
    | vdecl SCOLON                                  { Local (fst $1,snd $1,None) }
    | vdecl DEF init SCOLON                         { Local (fst $1,snd $1,Some $3) }
    | IF LPAR exp RPAR stmt    %prec THEN           { IfThenElse ($3,$5,Block []) }
    | IF LPAR exp RPAR stmt ELSE stmt               { IfThenElse ($3,$5,$7) }
    | FOR LPAR stmt exp SCOLON exp RPAR stmt        { For ($3,$4,$6,$8) }
    | WHILE LPAR exp RPAR stmt                      { While ($3,$5) }
    | DO stmt WHILE LPAR exp RPAR SCOLON            { DoWhile ($2,$5) }
    | ID COLON                                      { Label $1 }
    | GOTO ID SCOLON                                { Goto $2 }
    | SWITCH LPAR exp RPAR LCURL sstmts RCURL       { Switch ($3,$6) }
    | CONTINUE SCOLON                               { Continue }
    | BREAK SCOLON                                  { Break }
    | RETURN exp SCOLON                             { Return (Some $2) }
    | RETURN SCOLON                                 { Return None }
    | LCURL stmts RCURL                             { Block $2 }
    ;

stmts:             { [] }
     | stmt stmts  { $1::$2 }
     ;

sstmt: CASE VAL COLON  { Case $2 }
     | DEFAULT COLON   { Default }
     | stmt            { NormalStatement $1 }
     ;

sstmts:               { [] }
      | sstmt sstmts  { $1::$2 }
      ;
