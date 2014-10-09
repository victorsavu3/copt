open Prelude

type binop = Add | Sub | Mul | Div | Leq | Le | Geq | Gr | Eq | Neq | Asn

type lval =
  | Var   of string
  | Deref of expr
  | Field of lval * string
  | Index of lval * expr
and expr =
  | Val   of int
  | Lval  of lval
  | Addr  of lval
  | Binop of expr * binop * expr
  | App   of expr * expr list

type typ =
  | Int | Void
  | Struct of string
  | Ptr    of typ
  | Arr    of typ

type stmt =
  | Continue
  | Break
  | Return     of expr option
  | Local      of typ  * string * expr option
  | Expr       of expr
  | IfThenElse of expr * stmt * stmt
  | For        of expr * expr * expr * stmt
  | While      of expr * stmt
  | DoWhile    of stmt * expr
  | Label      of string
  | Goto       of string
  | Switch     of expr * (switch_stmt list)
  | Block      of stmt list
and switch_stmt =
  | Default
  | Case            of int
  | NormalStatement of stmt

type init = ExprInit of expr | ArrInit of int list
type decl =
  | StructDecl of string * (typ * string) list
  | Global     of typ * string * init option
  | Function   of typ * string * (typ * string) list * stmt list


(* helper functions *)

let binopToString = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Leq -> "<="
  | Le  -> "<"
  | Geq -> ">="
  | Gr  -> ">"
  | Eq  -> "=="
  | Neq -> "!="
  | Asn -> "="

let rec typToString = function
  | Int -> "int"
  | Void -> "void"
  | Struct x -> "struct "^x
  | Ptr t -> typToString t^" *"
  | Arr t -> typToString t^"[]"

let rec lvalToString = function
  | Var x -> x
  | Deref e -> exprToString e
  | Index (l,e) -> lvalToString l^"["^exprToString e^"]"
  | Field (l,n) -> lvalToString l^"."^n

and exprToString = function
  | Val x         -> string_of_int x
  | Lval x        -> lvalToString x
  | Addr x        -> lvalToString x
  | Binop (x,o,y) -> exprToString x^" "^binopToString o^" "^exprToString y
  | App (f, xs)   -> exprToString f^"("^funArgsToString xs^")"

and funArgsToString = function
    | [] -> ""
    | [x] -> exprToString x
    | x::xs -> exprToString x^", "^funArgsToString xs

and indent = List.map ((^)"\t")
and istmtToString x = indent @@ stmtToString x

and stmtToString = function
    | Continue -> ["continue;"]
    | Break -> ["break;"]
    | Return None -> ["return;"]
    | Return (Some x) -> ["return "^exprToString x^";"]
    | Local (t,x,None) -> [typToString t^" "^x^";"]
    | Local (t,x,Some e) -> [typToString t^" "^x^" = "^exprToString e^";"]
    | Expr e -> [exprToString e^";"]
    | IfThenElse (b,x,y) -> ("if ("^exprToString b^")") :: istmtToString x @ "else" :: istmtToString y
    | For (i,t,p,s) -> ("for ("^exprToString i^";"^exprToString t^";"^exprToString p^")") :: istmtToString s
    | While (b,s) -> ("while ("^exprToString b^")") :: istmtToString s
    | DoWhile (s,b) -> "do" :: istmtToString s @ ["while ("^exprToString b^");"]
    | Label s -> [s^":"]
    | Goto s  -> ["goto "^s^";"]
    | Switch (e,xs) -> ("switch ("^exprToString e^") {") :: sstmtToString xs @ ["}"]
    | Block xs -> "{" :: istmtsToString xs @ ["}"]

and sstmtToString = function
  | []                      -> []
  | Default::xs             -> "default:" :: sstmtToString xs
  | (Case x)::xs            -> ("case "^string_of_int x^":") :: sstmtToString xs
  | (NormalStatement s)::xs -> stmtToString s @ sstmtToString xs

and istmtsToString xs = List.concat @@ List.map istmtToString xs

let rec defsToString = function
  | [] -> "\n"
  | (t,x)::xs -> "\n\t"^typToString t^" "^x^";"^defsToString xs

let rec argToString = function
  | [] -> ""
  | [t,x] -> typToString t^" "^x
  | (t,x)::xs -> typToString t^" "^x^", "^argToString xs

let declToString = function
  | StructDecl (n,xs) -> "struct "^n^" {"^defsToString xs^"}\n"
  | Global  (t,n,None)  ->  typToString t^" "^n^";\n"
  | Global  (t,n,Some(ExprInit e))  ->  typToString t^" "^n^" = "^exprToString e^";\n"
  | Global  (t,n,Some(ArrInit xs))  ->  typToString t^" "^n^" = {"^String.concat ", " (List.map string_of_int xs)^"};\n"
  | Function (r,n,args,xs) -> typToString r^" "^n^"("^argToString args^") {\n"^String.concat "\n" (istmtsToString xs)^"\n}\n"

let rec declsToString = function
  | [] -> ""
  | x::xs -> declToString x^declsToString xs
