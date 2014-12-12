open Prelude
open Simc
open Printf
module Format = Legacy.Format

type node = int [@@deriving show]
type reg = string [@@deriving show]
(* type var = Reg of string | Mem of int *)
type action = Pos of expr | Neg of expr | Assign of reg * expr (* R := e *) | Load of reg * expr (* R = M[e]*) | Store of expr * expr (* M[e1] := e2*) | Skip | Call of string * expr list [@@deriving show]
type edge = node * action * node [@@deriving show]
type cfg = edge Set.t
module type Cfg = sig val cfg: cfg end

let start_node = 0
let node = ref start_node
let nn () = Ref.post_incr node (* gets a fresh node *)
let reg = ref 0
let reg_id id = "$R" ^ id (* register by id *)
let nr () = reg_id @@ string_of_int (Ref.post_incr reg) (* gets a fresh register *)
let ret_reg fname = reg_id ("ret_"^fname) (* return register for function *)
let ret_reg_main = ret_reg "main"  (* holds return code for the whole program *)

module FunNodes = struct
  let h : (string, node*node) Hashtbl.t = Hashtbl.create 16 (* start and end nodes for functions *)
  let add = Hashtbl.add h
  let find f = match Hashtbl.find h f with Some x -> x | None -> failwith @@ "Unknown function "^f
  let start_of = fst%find
  let end_of = snd%find
  let all () = Hashtbl.values h |> Set.of_enum
  let start_nodes () = Set.map fst @@ all ()
  let end_nodes () = Set.map snd @@ all ()
end

let init_nodes () = Set.add start_node (FunNodes.start_nodes ())

let start_nodes cfg = Set.diff (Set.map Tuple3.first cfg) (Set.map Tuple3.third cfg)
let end_nodes cfg = Set.diff (Set.map Tuple3.third cfg) (Set.map Tuple3.first cfg)
let nodes cfg = Set.union (Set.map Tuple3.first cfg) (Set.map Tuple3.third cfg)
let out_edges n = Set.filter ((=) n % Tuple3.first)
let in_edges n = Set.filter ((=) n % Tuple3.third)

let reachable_from x cfg =
  let rec dfs seen x =
    if Set.mem x seen then Set.empty else
    out_edges x cfg
    |> comp21 Set.union @@ ExtSet.flat_map (dfs (Set.add x seen) % Tuple3.third)
  in dfs Set.empty x
let is_reachable_from v u cfg = Set.mem v @@ nodes @@ reachable_from u cfg
let fun_edges f cfg = reachable_from (FunNodes.start_of f) cfg

(* error processing the cfg *)
exception Cfg of string

let fold_actions : action list -> node -> node * edge list = fun aa u ->
  List.fold_right (fun a (u,ks) ->
    let v = nn () in
    v, (u, a, v)::ks
  ) aa (u, [])

(*expr_need_split : expr -> bool*)
let rec expr_need_split = function
  | Lval (Deref _) | Lval (Index _) -> true
  | Lval (Var _) | Val _ | ArrInit _ -> false
  | Binop (e1,op,e2) -> op = Asn || expr_need_split e1 || expr_need_split e2
  | Lval (Field _) | Addr _ | App _ -> true

let var reg = Lval (Var (Some Local,reg))

let from_nm_expr (u,edges) e = match e with
  | Lval (Var _) | Val _ -> u, edges, e (* trivial assignments *)
  | expr -> let v = nn () in let r = nr () in v, Set.add (u,Assign (r,expr),v) edges, var r

type location = LOC_var of reg | LOC_addr of expr

let rec from_lval (u,edges) = function
  | Var (loc,x) -> u, edges, LOC_var x
  | Deref expr ->
      let v,edges,r = from_expr (u,edges) expr in
      v, edges, LOC_addr r
  | Field (lval,field) ->
      let v,edges,ra = from_lval (u,edges) lval in
      let ra = match ra with LOC_var r -> var r | LOC_addr r -> r in
      let dv = nn () in let dr = nr () in
      let offs = raise Not_implemented in (* we need some environment to keep the fields and their size *)
      let ld_expr = Binop (ra, Add, offs) in
      let edges = Set.add (v,Assign (dr,ld_expr),dv) edges in
      dv,edges,LOC_addr (var dr)
  | Index (lval,expr) ->
      let v,edges,ra = from_lval (u,edges) lval in
      let w,edges,ri = from_expr (v,edges) expr in
      let ra = match ra with LOC_var r -> var r | LOC_addr r -> r in
      let dv = nn () in let dr = nr () in
      let ld_expr = Binop (ra, Add, ri) in
      let edges = Set.add (w,Assign (dr,ld_expr),dv) edges in
      dv,edges,LOC_addr (var dr)

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
  | App (f, args) ->
      let v,edges,fp = from_expr (u,edges) f in
      let fname = match fp with
        | Lval (Var (Some Global, fname)) -> fname
        | Lval (Var (_, fname)) -> raise @@ Cfg "Locality of function must be Global"
        | _ -> raise @@ Cfg "Could not compute function expression"
      in
      let w,edges,ld_args = List.fold_left (fun (an,aes,rs) e -> let n,es,r = from_expr (an,aes) e in n,es,(r::rs)) (v,edges,[]) args in
      let x = nn () in
      let edges = Set.add (w, Call (fname, ld_args), x) edges in
      let y = nn () in
      let r = nr () in (* returned result must be saved in new register *)
      let edges = Set.add (x, Assign (r, var @@ ret_reg fname), y) edges in
      y,edges,var r
  | _ -> raise Not_implemented

type context = { continue: node option; break: node option; return: node; return_reg: reg option }
let rec from_stmt ctx (u,edges) stmt =
  match stmt with
  | Nop ->
      let v = nn () in
      let edges = Set.add (u, Skip, v) edges in
      v,edges
  | Continue when ctx.continue=None -> raise @@ Cfg "Continue was used outside of context!"
  | Break when ctx.break=None -> raise @@ Cfg "Break was used outside of context!"
  | Continue -> (Option.get ctx.continue, Set.add (u, Skip, Option.get ctx.continue) edges)
  | Break -> (nn (), Set.add (u, Skip, Option.get ctx.break) edges)
  | Return None -> (nn (), Set.add (u, Skip, ctx.return) edges)
  | Return (Some expr) ->
      let v,edges,r = from_expr (u,edges) expr in
      let action = match ctx.return_reg with
        | Some r' -> Assign (r', r)
        | None -> Skip
      in
      let edges = Set.add (v, action, ctx.return) edges in
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
      let v1,edges = from_stmt ctx (u,edges) i in
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
  | DoWhile (s,b) ->
      let fn = nn () in
      let tv,edges = from_stmt {ctx with continue = Some u; break = Some fn} (u,edges) s in
      let bv,edges,r = from_expr (tv,edges) b in
      let edges = Set.union (Set.of_list [bv, Pos(r), u; bv, Neg(r), fn]) edges in
      fn,edges
  | Label l -> raise Not_implemented
  | Goto l -> raise Not_implemented
  | Switch (b, ss) -> raise Not_implemented
  | LocalDecl (t,x,Some expr) ->
      let v,edges,r = from_expr (u,edges) expr in
      let w = nn () in
      let edges = Set.add (v, Assign (x, r), w) edges in
      w,edges
  | LocalDecl (t,x,None) -> (u,edges)
  | Block ss -> from_stmts ctx (u,edges) ss
and from_stmts ctx (u,edges) = List.fold_left (from_stmt ctx) (u,edges)

(*cfg for one declaration*)
let from_decl (u,edges) = function
  | StructDecl(name, decls) -> raise Not_implemented
  | GlobalDecl (t, name, Some expr) ->
      let v,edges,r = from_expr (u,edges) expr in
      let w = nn () in
      let edges = Set.add (v, Assign (name, r), w) edges in
      w,edges
  | FunDecl (r,name,args,stmts) ->
      let u = nn () in
      let v = nn () in
      FunNodes.add name (u,v);
      let return_reg = match r with Void -> None | _ -> Some (ret_reg name) in
      let ctx = { continue = None; break = None; return = v; return_reg } in
      let v2,edges = from_stmts ctx (u, edges) stmts in
      let edges = Set.add (v2, Skip, v) edges in
      v,edges
  | _ -> u,edges (* nothing to do if there is just a declaration without init *)

(*cfg for the whole program*)
let from_decls decls =
  let funs, globs = List.partition (function FunDecl _ -> true | _ -> false) decls in
  let mainfuns = List.filter (function FunDecl(_,"main",_,_) -> true | _ -> false) funs in
  let main = Option.get_exn (List.hd mainfuns) (Cfg "There must be exactly one function called main") in
  if Config.no_fun then
    if List.length globs <> 0 then raise @@ Cfg "Config.no_fun: globals are not supported" else
    snd @@ from_decl (-1, Set.empty) main (* Note: start node is ignored for functions, so just using -1 *)
  else
    let u = nn () in (* start node of the whole CFG *)
    let v = nn () in (* end node of the whole CFG *)
    let w,edges = List.fold_left from_decl (u,Set.empty) globs in (* initialize globals *)
    let edges = Set.add (w, Call ("main", []), v) edges in (* implicit call to main *)
    snd @@ List.fold_left from_decl (-1,edges) funs (* function bodies *)


(* pretty printing of cfg *)
let pretty_action = function
  | Pos e -> sprintf "Pos (%s)" @@ exprToString e
  | Neg e -> sprintf "Neg (%s)" @@ exprToString e
  | Assign (v,e) -> sprintf "%s := %s" v @@ exprToString e
  | Load (v,e) -> sprintf "%s := M[%s]" v @@ exprToString e
  | Store (e1,e2) -> sprintf "M[%s] := %s" (exprToString e1) (exprToString e2)
  | Skip -> "Skip"
  | Call (name, args) -> sprintf "Call %s(%s)" name (String.concat ", " @@ List.map exprToString args)

let pretty_edge (u,l,v) =
  sprintf "\t%d -> %d [label=\"%s\"]\n" u v (pretty_action l)

let pretty_node (u, l) =
  sprintf "\t%d [xlabel=\"%s\"]\n" u (String.escaped l)

let pretty_cfg ?node_labels cfg =
  let nodes = String.concat "" (List.map pretty_node (node_labels |? [])) in
  let edges = String.concat "" (List.map pretty_edge (Set.to_list cfg)) in
  sprintf "digraph {\n%s%s}" nodes edges

(* collect expressions *)
let exprs_of_action = function
  | Pos e | Neg e | Assign (_,e) | Load (_,e) -> Set.singleton e
  | Store (e1,e2) -> Set.union (Set.singleton e1) (Set.singleton e2)
  | Call (n,args) -> List.fold_left (flip Set.add) Set.empty args
  | Skip -> Set.empty
let exprs_of_cfg : cfg -> expr Set.t = ExtSet.flat_map (fun (_,a,_) -> exprs_of_action a)

(* collect l-values *)
let rec lvals_of_lval = function
  | Deref e -> lvals_of_expr e
  | Field (l,f) -> lvals_of_lval l
  | Index (l,e) -> Set.union (lvals_of_lval l) (lvals_of_expr e)
  | l -> Set.singleton l
and lvals_of_expr = function
  | Val _ | ArrInit _ -> Set.empty
  | Lval l | Addr l -> Set.add l (lvals_of_lval l)
  | Binop (a,o,b) -> Set.union (lvals_of_expr a) (lvals_of_expr b)
  | App (f, args) -> List.fold_left (flip @@ Set.union % lvals_of_expr) (lvals_of_expr f) args

(* collect variables *)
let rec vars_of_lval = function
  | Var (Some l,r) -> Set.singleton (l,r)
  | Var (None, r) -> failwith @@ "Undeclared variable "^r
  | Deref e -> vars e
  | Field (l,f) -> vars_of_lval l
  | Index (l,e) -> Set.union (vars_of_lval l) (vars e)
and vars e = ExtSet.flat_map vars_of_lval (lvals_of_expr e)
let vars_of_cfg cfg = ExtSet.flat_map vars (exprs_of_cfg cfg)

(* collect registers *)
let rec regs_of_lval = function
  | Var (loc,r) -> Set.singleton r
  | Deref e -> regs e
  | Field (l,f) -> regs_of_lval l
  | Index (l, e) -> Set.union (regs_of_lval l) (regs e)
and regs e = ExtSet.flat_map regs_of_lval (lvals_of_expr e)
let regs_of_cfg cfg = ExtSet.flat_map regs (exprs_of_cfg cfg)

(* collect assigns *)
let assign_of_action = function
  | Assign (r, e) -> Set.singleton (r, e)
  | _ -> Set.empty
let assigns_of_cfg : cfg -> (reg*expr) Set.t = ExtSet.flat_map (fun (u,a,v) -> assign_of_action a)

(* map expr *)
type map_t = Mlval of (lval -> lval) | Mexpr of (expr -> expr) | Mreg of (reg -> reg)
let rec map_lval : map_t -> lval -> lval = fun f l ->
  let lval = map_lval f in
  let expr = map_expr f in
  let f_lval = match f with
    | Mlval g -> g
    | _ -> identity
  in
  f_lval @@ match l with
  | Var (loc,x) -> Var (loc,x)
  | Deref x -> Deref (expr x)
  | Field (l, s) -> Field (lval l, s)
  | Index (l, x) -> Index (lval l, expr x)
and map_expr : map_t -> expr -> expr = fun f e ->
  let lval = map_lval f in
  let expr = map_expr f in
  let f_expr = match f with
    | Mexpr g -> g
    | _ -> identity
  in
  f_expr @@ match e with
  | Val x -> Val x
  | ArrInit x -> ArrInit x
  | Lval l -> Lval (lval l)
  | Addr l -> Addr (lval l)
  | Binop (e1, op, e2) -> Binop (expr e1, op, expr e2)
  | App (f, args) -> App (expr f, List.map expr args)
and map_action : map_t -> action -> action = fun f a ->
  let expr = map_expr f in
  let reg = match f with
    | Mreg g -> g
    | _ -> identity
  in
  match a with
  | Pos e -> Pos (expr e)
  | Neg e -> Neg (expr e)
  | Assign (r, e) -> Assign (reg r, expr e)
  | Load (r, e) -> Load (reg r, expr e)
  | Store (e1, e2) -> Store (expr e1, expr e2)
  | Call (n, args) -> Call (n, List.map expr args)
  | Skip -> Skip
let map_edge f (u,a,v) = u, map_action f a, v
