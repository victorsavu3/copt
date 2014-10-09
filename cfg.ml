open Prelude
open Simc
open Printf

type node = int
type reg = string
(* type var = Reg of string | Mem of int *)
type action = Pos of expr | Neg of expr | Assign of reg * expr (* R := e *) | Load of reg * expr (* R = M[e]*) | Store of expr * expr (* M[e1] := e2*) | Skip
type edge = node * action * node
type cfg = edge Set.t

let node = ref 0
let nn () = incr node; !node (* gets a fresh node *)
let reg = ref 0
let nr () = incr reg; "__R" ^ string_of_int (!reg) (* gets a fresh register *)

(* error processing the cfg *)
exception Cfg of string

(*expr_need_split : expr -> bool*)
let rec expr_need_split = function
  | Lval (Deref _) | Lval (Index _) -> true
  | Lval (Var _) | Val _ -> false
  | Binop (e1,op,e2) -> op = Asn || expr_need_split e1 || expr_need_split e2
  | Lval (Field _) | Addr _ | App _ -> raise Not_implemented

let var reg = Lval (Var reg)

let from_nm_expr (u,edges) e = match e with
  | Lval (Var _) | Val _ -> u, edges, e (* trivial assignments *)
  | expr -> let v = nn () in let r = nr () in v, Set.add (u,Assign (r,expr),v) edges, var r

type location = LOC_var of reg | LOC_addr of expr

let rec from_lval (u,edges) = function
  | Var x -> u, edges, LOC_var x
  | Deref expr ->
      let v,edges,r = from_expr (u,edges) expr in
      v, edges, LOC_addr r
  | Field _ -> raise Not_implemented
  | Index (lval,expr) ->
      let v,edges,ra = from_lval (u,edges) lval in
      let w,edges,ri = from_expr (v,edges) expr in
      let ra = match ra with LOC_var r -> Lval (Var r) | LOC_addr r -> r in
      let dv = nn () in let dr = nr () in
      let ld_expr = Binop (ra, Add, ri) in
      let edges = Set.add (w,Assign (dr,ld_expr),dv) edges in
      dv,edges,LOC_addr (Lval (Var dr))

and from_expr (u,edges) : expr -> node * cfg * expr = function
  | expr when not @@ expr_need_split expr -> from_nm_expr (u,edges) expr
  | Lval (Deref expr) ->
      let v,edges,r = from_expr (u,edges) expr in
      let dv = nn () in let dr = nr () in
      let edges = Set.add (v,Load (dr,r),dv) edges in
      dv,edges,var dr
  | Lval (Index (lval,expr)) ->
      let v,edges,ra = from_expr (u,edges) (Lval lval) in
      let w,edges,ri = from_expr (v,edges) expr in
      let dv = nn () in let dr = nr () in
      let ld_expr = Binop (ra, Add, ri) in
      let edges = Set.add (w,Load (dr,ld_expr),dv) edges in
      dv,edges,var dr
  | Binop (Lval l1,Asn,e2) ->
      let v,edges,loc = from_lval (u,edges) l1 in
      let w,edges,r2 = from_expr (v,edges) e2 in
      let dv = nn () in
      let act = match loc with
        | LOC_var r -> Assign (r,r2)
        | LOC_addr r -> Store (r,r2)
      in
      let edges = Set.add (w,act,dv) edges in
      dv,edges,r2
  | Binop (_,Asn,e2) -> raise @@ Cfg "Assignment to non-lval"
  | Binop (e1,op,e2) ->
      let v,edges,r1 = from_expr (u,edges) e1 in
      let w,edges,r2 = from_expr (v,edges) e2 in
      let dv = nn () in let dr = nr () in
      let ld_expr = Binop (r1, op, r2) in
      let edges = Set.add (w,Assign (dr,ld_expr),dv) edges in
      dv,edges,var dr
  | _ -> raise Not_implemented

type context = { continue: node option; break: node option; return: node }
let rec from_stmt ctx (u,edges) stmt =
  match stmt with
  | Continue when ctx.continue=None -> raise @@ Cfg "Continue was used outside of context!"
  | Break when ctx.break=None -> raise @@ Cfg "Break was used outside of context!"
  | Continue -> (Option.get ctx.continue, Set.add (u, Skip, Option.get ctx.continue) edges)
  | Break -> (nn (), Set.add (u, Skip, Option.get ctx.break) edges)
  | Return None -> (nn (), Set.add (u, Skip, ctx.return) edges)
  | Return (Some expr) ->
      let v,edges,r = from_expr (u,edges) expr in
      let edges = Set.add (v, Skip, ctx.return) edges in
      nn (),edges
  | Expr expr ->
      let v,edges,r = from_expr (u,edges) expr in
      (v,edges)
  | IfThenElse(b, tb, fb) ->
      let bv,edges,r = from_expr (u,edges) b in
      let tn = nn () in
      let fn = nn () in
      let en = nn () in
      let tv,edges = from_stmt ctx (tn,edges) tb in
      let fv,edges = from_stmt ctx (fn,edges) fb in
      let edges = Set.union (Set.of_list [bv, Pos(r), tn; bv, Neg(r), fn; tv, Skip, en; fv, Skip, en]) edges in
      (en,edges)
  | For(i,b,c,s) ->
      let v1,edges = from_stmt ctx (u,edges) (Expr i) in
      let v2,edges,r = from_expr (v1,edges) b in
      let fn = nn () in
      let tn = nn () in
      let v4 = nn () in
      let v3,edges = from_stmt {ctx with continue = Some v4; break = Some fn} (tn,edges) s in
      let v5,edges = from_stmt ctx (v4,edges) (Expr c) in
      let edges = Set.union (Set.of_list [
          v2, Pos(r), tn;
          v2, Neg(r), fn;
          v3, Skip, v4;
          v5, Skip, v1
        ]) edges
      in
      fn,edges
  | While(b,s) ->
      let bv,edges,r = from_expr (u,edges) b in
      let tn = nn () in
      let fn = nn () in
      let tv,edges = from_stmt {ctx with continue = Some u; break = Some fn} (tn,edges) s in
      let edges = Set.union (Set.of_list [bv, Pos(r), tn; bv, Neg(r), fn; tv, Skip, u]) edges in
      fn,edges
  | DoWhile (s,b) -> raise Not_implemented
  | Label l -> raise Not_implemented
  | Goto l -> raise Not_implemented
  | Switch (b, ss) -> raise Not_implemented
  | Local (t,x,Some expr) -> raise Not_implemented
  | Local (t,x,None) -> (u,edges)
  | Block ss -> from_stmts ctx (u,edges) ss
and from_stmts ctx (u,edges) = List.fold_left (from_stmt ctx) (u,edges)

(*cfg for the whole program*)
let from_decls decls =
  let xs = List.filter_map (function
    | Function(r,"main",args,stmts) ->
        let u = nn () in
        let v = nn () in
        let ctx = { continue = None; break = None; return = v} in
        let v2,xs = from_stmts ctx (u,Set.empty) stmts in
        let xs = Set.add (v2,Skip,v) xs in Some xs
    | _ -> None
    ) decls
  in
  if List.length xs <> 1 then
    raise @@ Cfg "There must be exactly one function called main"
  else
    List.hd xs

(* pretty printing of cfg *)
let pretty_action = function
  | Pos e -> sprintf "Pos (%s)" @@ exprToString e
  | Neg e -> sprintf "Neg (%s)" @@ exprToString e
  | Assign (v,e) -> sprintf "%s := %s" v @@ exprToString e
  | Load (v,e) -> sprintf "%s := M[%s]" v @@ exprToString e
  | Store (e1,e2) -> sprintf "M[%s] := %s" (exprToString e1) (exprToString e2)
  | Skip -> "Skip"

let pretty_edge (u,l,v) =
  sprintf "%d -> %d [label=\"%s\"] \n" u v (pretty_action l)

let pretty_cfg cfg =
  let edges = String.concat "" (List.map pretty_edge (Set.to_list cfg)) in
  sprintf "digraph {
    %s
  }" edges
