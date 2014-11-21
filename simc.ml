open Prelude
module Format = Legacy.Format (* BatFormat.asprintf is missing, but needed for ppx_deriving *)

type binop = Add | Sub | Mul | Div | Mod | Leq | Le | Geq | Gr | Eq | Neq | Asn [@@deriving show]

let b2i f a b = if f a b then 1 else 0
let fun_of_op = function
  | Add -> (+) | Sub -> (-) | Mul -> ( * ) | Div -> (/) | Mod -> (mod)
  | Leq -> b2i (<=) | Le -> b2i (<) | Geq -> b2i (>=) | Gr -> b2i (>) | Eq -> b2i (=) | Neq -> b2i (<>)
  | Asn -> fun a b -> b

type lval =
  | Var   of string
  | Deref of expr
  | Field of lval * string
  | Index of lval * expr
  [@@deriving show]
and expr =
  | Val   of int
  | ArrInit of int list
  | Lval  of lval
  | Addr  of lval
  | Binop of expr * binop * expr
  | App   of expr * expr list
  [@@deriving show]

type typ =
  | Int | Void
  | Struct of string
  | Ptr    of typ
  | Arr    of typ
  [@@deriving show]

type stmt =
  | Nop
  | Continue
  | Break
  | Return     of expr option
  | Local      of typ  * string * expr option
  | Expr       of expr
  | IfThenElse of expr * stmt * stmt
  | For        of stmt * expr * expr * stmt
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

type decl =
  | StructDecl of string * (typ * string) list
  | Global     of typ * string * expr option
  | Function   of typ * string * (typ * string) list * stmt list


(* helper functions *)
let rec reg_in_expr reg = function
  | Binop (e1,op,e2) -> reg_in_expr reg e1 || reg_in_expr reg e2
  | App (f, args) -> reg_in_expr reg f || List.exists (reg_in_expr reg) args
  | Lval lval | Addr lval -> reg_in_lval reg lval
  | Val _ | ArrInit _ -> false
and reg_in_lval reg = function
  | Var name -> reg=name
  | Deref e -> reg_in_expr reg e
  | Field (b, name) -> reg_in_lval reg b
  | Index (b, i) -> reg_in_lval reg b || reg_in_expr reg i

let binopToString = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Mod -> "%"
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
  | ArrInit xs    -> "{"^String.concat ", " (List.map string_of_int xs)^"}"
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
    | Nop -> [";"]
    | Continue -> ["continue;"]
    | Break -> ["break;"]
    | Return None -> ["return;"]
    | Return (Some x) -> ["return "^exprToString x^";"]
    | Local (t,x,None) -> [typToString t^" "^x^";"]
    | Local (t,x,Some e) -> [typToString t^" "^x^" = "^exprToString e^";"]
    | Expr e -> [exprToString e^";"]
    | IfThenElse (b,x,y) -> ("if ("^exprToString b^")") :: istmtToString x @ "else" :: istmtToString y
    | For (i,t,p,s) -> ("for ("^String.concat " " (stmtToString i)^";"^exprToString t^";"^exprToString p^")") :: istmtToString s
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
  | Global  (t,n,Some e)  ->  typToString t^" "^n^" = "^exprToString e^";\n"
  | Function (r,n,args,xs) -> typToString r^" "^n^"("^argToString args^") {\n"^String.concat "\n" (istmtsToString xs)^"\n}\n"

let rec declsToString = function
  | [] -> ""
  | x::xs -> declToString x^declsToString xs
