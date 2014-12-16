open Prelude
module Format = Legacy.Format (* BatFormat.asprintf is missing, but needed for ppx_deriving *)

type binop = Add | Sub | Mul | Div | Mod | Leq | Le | Geq | Gr | Eq | Neq | Asn [@@deriving show]

let b2i f a b = if f a b then 1 else 0
let fun_of_op = function
  | Add -> (+) | Sub -> (-) | Mul -> ( * ) | Div -> (/) | Mod -> (mod)
  | Leq -> b2i (<=) | Le -> b2i (<) | Geq -> b2i (>=) | Gr -> b2i (>) | Eq -> b2i (=) | Neq -> b2i (<>)
  | Asn -> fun a b -> b

type locality = Local | Global [@@deriving show]
type lval =
  | Var   of locality option * string
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
  | LocalDecl  of typ  * string * expr option
  | Expr       of expr
  | IfThenElse of expr * stmt * stmt
  | For        of stmt * expr * expr * stmt
  | While      of expr * stmt
  | DoWhile    of stmt * expr
  | Label      of string
  | Goto       of string
  | Switch     of expr * (switch_stmt list)
  | Block      of stmt list
  [@@deriving show]
and switch_stmt =
  | Default
  | Case            of int
  | NormalStatement of stmt
  [@@deriving show]

type decl =
  | StructDecl of string * (typ * string) list
  | GlobalDecl of typ * string * expr option
  | FunDecl    of typ * string * (typ * string) list * stmt list
  [@@deriving show]


(* helper functions *)
let map_stmts f ast =
  let map_fun = function
    | FunDecl (r,n,args,xs) -> FunDecl (r,n,args, List.map f xs)
    | d -> d
  in
  List.map map_fun ast

let rec reg_in_expr reg = function
  | Binop (e1,op,e2) -> reg_in_expr reg e1 || reg_in_expr reg e2
  | App (f, args) -> reg_in_expr reg f || List.exists (reg_in_expr reg) args
  | Lval lval | Addr lval -> reg_in_lval reg lval
  | Val _ | ArrInit _ -> false
and reg_in_lval reg = function
  | Var (loc,name) -> reg=name
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
  | Var (loc,x) -> x
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
    | LocalDecl (t,x,None) -> [typToString t^" "^x^";"]
    | LocalDecl (t,x,Some e) -> [typToString t^" "^x^" = "^exprToString e^";"]
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
  | GlobalDecl  (t,n,None)  ->  typToString t^" "^n^";\n"
  | GlobalDecl  (t,n,Some e)  ->  typToString t^" "^n^" = "^exprToString e^";\n"
  | FunDecl (r,n,args,xs) -> typToString r^" "^n^"("^argToString args^") {\n"^String.concat "\n" (istmtsToString xs)^"\n}\n"

let rec declsToString = function
  | [] -> ""
  | x::xs -> declToString x^declsToString xs

let astToString = String.concat "\n" % List.map (no_prefix%show_decl)

module Locality : sig
  val decls: decl list -> decl list
end = struct
  type t = (string, locality) Map.t

  let local vname = Map.add vname Local
  let global vname = Map.add vname Global

  let fold : (t -> 'a -> t*'a) -> t -> 'a list -> 'a list =
    fun f m xs -> snd @@ List.fold_left (fun (m,xs') x -> let m',x' = f m x in m',xs'@[x']) (m,[]) xs

  let rec lval m : lval -> lval = function
    | Var(None, n) -> 
      (
      match Map.find n m with
        | None -> ?? "Variable used before declaration"
        | l -> Var(l, n)
      )
    | Deref(e) -> Deref(expr m e)
    | Field(l, n) -> Field(lval m l, n)
    | Index(l, e) -> Index(lval m l, expr m e)
    | v -> v
  and expr m : expr -> expr = function
    | Lval(v) -> Lval(lval m v)
    | Addr(v) -> Addr(lval m v)
    | Binop(e1, o, e2) -> Binop(expr m e1, o, expr m e2)
    | App(e, el) -> App(expr m e, exprs m el)
    | e -> e
  and exprs m = List.map (expr m)

  let rec stmt m = function
    | LocalDecl (t,x,None) -> local x m, LocalDecl (t,x,None)
    | LocalDecl (t,x,Some(e)) -> local x m, LocalDecl (t,x, Some(expr m e))
    | Label s -> local s m, Label s
    
    | Return (Some(e)) -> m, Return (Some(expr m e))
    | Expr(e) -> m, Expr(expr m e)
    | IfThenElse (b,x,y) -> m, IfThenElse (expr m b, stmt_convert m x, stmt_convert m y)
    | For (i,t,p,s) -> 
      let mf, ip = stmt m i in
      m, For (ip, expr mf t,expr mf p,stmt_convert mf s)
    | While (b,s) -> m, While (expr m b, stmt_convert m s)
    | DoWhile (s,b) -> m, DoWhile (stmt_convert m s, expr m b)
    | Goto s  -> 
      (
        match Map.find s m with
          | None -> ?? "Jump to undefined label"
          | Some(Local) -> m, Goto s
          | Some(Global) -> ?? "Global labels should not exist"
      )
    | Block(xs) -> m, Block(stmts m xs)
    | Switch (e,xs) -> m, Switch (expr m e, stmt_switch m xs)
    
    | s -> m, s
  and stmt_switch m = function 
    | [] -> []
    | (NormalStatement s)::xs -> [NormalStatement(stmt_convert m s)] @ stmt_switch m xs
    | s::xs -> stmt_switch m xs
  and stmt_convert m s =
    let (m, s) = stmt m s in s
  and stmts m : stmt list -> stmt list = fold stmt m

  let rec process_args m = function
    | [] -> m
    | (t, n)::xs -> process_args (local n m) xs

  let decl m = function
    | GlobalDecl (t,n,None) -> global n m, GlobalDecl (t,n,None)
    | GlobalDecl (t,n,Some(e)) -> global n m, GlobalDecl (t,n,Some(expr m e))
    | FunDecl (r,n,args,xs) -> 
      let mf = global n m in
      let mp = process_args mf args in
      mf, FunDecl (r,n,args, stmts mp xs)
    | s -> m, s

  let extern_funs = ["printf"] (* TODO this should depend on the included header files *)
  let init = List.fold_left (fun m f -> Map.add f Global m) Map.empty extern_funs
  let decls = fold decl init
end
