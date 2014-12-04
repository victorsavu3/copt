open Prelude
open Cfg
open Solver

(* some analyses need the Cfg to generate bot of the used domain! *)
module type S = functor (C: Cfg) -> sig
  module Ana : Framework
  val vals: ConstraintSystem(Ana.D).valuation
end

let pretty_ana (module A: S) cfg =
  let module Asol = A (struct let cfg = cfg end) in
  let str u = Asol.vals u |> Asol.Ana.D.show |> Domain.no_prefix in
  let nl = List.map (fun u -> u, str u) (nodes cfg |> Set.elements) in
  pretty_cfg ~node_labels:nl cfg

module AvailExpr (Memo: sig val is_memo: reg -> bool end) (C: Cfg) = struct
  module Ana = struct
    let dir = `Fwd
    module D = Domain.ExprMustSet (C)
    let init = D.empty

    (* we assume this is done after the memorization transformation *)
    let effect a d = match a with
      (*| _ -> ?? "Exercise 3.2b"*)
      | Assign (r, e) when Memo.is_memo r ->
          D.add e d |> D.filter (neg @@ Simc.reg_in_expr r)
      | Assign (r, e)
      | Load (r, e) ->
          D.filter (neg @@ Simc.reg_in_expr r) d
      | _ -> d
  end

  module Csys = CsysGenerator (Ana)
  let vals = Csys.solve C.cfg
  let available_at e u = Ana.D.mem e (vals u)
end

module Liveness (C: Cfg) = struct
  module Ana = struct
    let dir = `Bwd (*?? "Exercise 4.1b"*)
    module D = Domain.RegMaySet
    let init = D.empty (*?? "Exercise 4.1b"*)

    let effect a d =
      let dregs = D.of_set % regs in
      match a with
      (*| _ -> ?? "Exercise 4.1b"*)
      | Skip -> d
      | Pos (e) | Neg (e) -> D.union d (dregs e)
      | Assign (r, e)
      | Load (r, e) ->
          (* this is true liveness *)
          D.remove r d |> D.union (if D.mem r d then dregs e else D.empty)
      | Store (e1, e2) -> D.union d @@ D.union (dregs e1) (dregs e2)
      | Call (r, n, args) -> List.fold_left (flip @@ D.union % dregs) d args
  end

  module Csys = CsysGenerator (Ana)
  let vals = Csys.solve C.cfg
  let live_at r u = Ana.D.mem r (vals u)
  let dead_at r u = not @@ live_at r u
end

module ConstProp (C: Cfg)= struct
  open Simc
  module Ana = struct
    let dir = `Fwd
    module V = Domain.FlatInt
    module D = Domain.RegMap.Must (V)
    let init = D.top

    let effect_binop e1 op e2 = match e1,op,e2 with
      | _, Asn, _ -> raise @@ Cfg "Assignments as expressions should no longer be in the CFG!"
      | V.Val a, op, V.Val b -> V.Val (fun_of_op op a b)
      | _ -> V.Top
    let rec effect_expr e m = match e with
      | Val i -> V.Val i
      | Lval (Var r) -> D.find r m
      | Binop (e1, op, e2) -> effect_binop (effect_expr e1 m) op (effect_expr e2 m)
      | _ -> V.Top
    let effect a d =
      (*?? "Exercise 6.2a" (* you can use fun_of_op for evaluating binops *)*)
      match d with D.Bot -> D.Bot | D.Vals m ->
      match a with
      | Skip -> d
      | Pos (e) -> (match effect_expr e m with V.Val 0 -> D.Bot | _ -> d)
      | Neg (e) -> (match effect_expr e m with V.Val x when x<>0 -> D.Bot | _ -> d)
      | Assign (r, e) -> D.Vals (D.add r (effect_expr e m) m)
      | Load (r, e) -> D.Vals (D.add r V.Top m)
      | Store (e1, e2) -> d
      | Call _ -> d (* assume that calls don't change registers (used for debug printfs) *)
  end

  module Csys = CsysGenerator (Ana)
  let vals = Csys.solve C.cfg
  let dead_at u = vals u = Ana.D.Bot
  let const u e =
    match vals u with Ana.D.Bot -> e | Ana.D.Vals m ->
      let rec lval = function
        | Deref x -> Deref (expr x)
        | Field (l, s) -> Field (lval l, s)
        | Index (l, x) -> Index (lval l, expr x)
        | x -> x
      and expr e =
        match Ana.effect_expr e m with Ana.V.Val i -> Val i | _ -> match e with
          | Lval l -> Lval (lval l)
          | Addr l -> Addr (lval l)
          | Binop (e1, op, e2) -> Binop (expr e1, op, expr e2)
          | App (f, args) -> App (expr f, List.map expr args)
          | x -> x
      in
      expr e
end

module FlowInsensitiveAlias = struct
  open Simc
  module UnionFind (K: sig type t val order: t*t -> t*t end) : sig
    type t
    val create: unit -> t
    val add: t -> K.t -> unit
    val find: t -> K.t -> K.t
    val union: t -> K.t -> K.t -> unit
  end = struct
    type t = { 
      mutable ct : int; 
      mutable mapping : (K.t, int) Hashtbl.t; 
      mutable rev_mapping : (int, K.t) Hashtbl.t; 
      mutable parents : (int, int) Hashtbl.t; 
      mutable size : (int, int) Hashtbl.t
    }
    let create () = 
      {parents=Hashtbl.create 20; size=Hashtbl.create 20; ct=1; mapping=Hashtbl.create 20; rev_mapping=Hashtbl.create 20}
    
    let add t e =
      Hashtbl.add t.parents t.ct t.ct;
      Hashtbl.add t.size t.ct 1;
      Hashtbl.add t.mapping e t.ct;
      Hashtbl.add t.rev_mapping t.ct e;
      t.ct <- t.ct + 1;;
    
    (* helpers *)
    let mapping t e = Option.get @@ Hashtbl.find t.mapping e
    let rev_mapping t e = Option.get @@ Hashtbl.find t.rev_mapping e
    
    let set_parent t e1 e2 = (* parent of e1 is e2 *)
      let e2s = Option.get @@ Hashtbl.find t.size e2 in
      let pe1 = Option.get @@ Hashtbl.find t.parents e1 in
      let pe1s = Option.get @@ Hashtbl.find t.size pe1 in
      Hashtbl.replace t.size pe1 (pe1s - 1);
      Hashtbl.replace t.size e2 (e2s + 1);
      Hashtbl.replace t.parents e1 e2;;
    
    let swap_mapping t e1 e2 =
      let e1m = Option.get @@ Hashtbl.find t.mapping e1 in
      let e2m = Option.get @@ Hashtbl.find t.mapping e2 in
      Hashtbl.replace t.mapping e1 e2m;
      Hashtbl.replace t.mapping e2 e1m;
      Hashtbl.replace t.rev_mapping e2m e1;
      Hashtbl.replace t.rev_mapping e1m e2;;
    
    let find t e = 
      let rec find' t e =
        let p = Option.get @@ Hashtbl.find t e in
        if p == e then 
          e
        else
          find' t p
      in
      let rec update_parens t e top =
        if e != top then
          let p = Option.get @@ Hashtbl.find t.parents e in
          set_parent t e top;
          update_parens t p top
      in
      let me = mapping t e in
      let r = find' t.parents me in
      update_parens t me r;
      rev_mapping t r
    
    let union t e1 e2 =  
      let size t e = Option.get @@ Hashtbl.find t.size (mapping t e) in
      let (l, g) = 
        if size t e1 > size t e2 then 
          (e2, e1) 
        else 
          (e1, e2) 
      in
      set_parent t (mapping t l) (mapping t g);
      let (e1, e2) = K.order(l, g) in
      if e1 != l then
        swap_mapping t e1 e2
  end
  type key = Reg of reg | Mem of reg
  module UF = UnionFind (struct
    type t = key
    let order (x,y) = match x,y with Reg _, Mem _ -> y,x | _ -> x,y
  end)
  (* prints equivalence classes to stderr *)
  let debug cfg =
    let regs = regs_of_cfg cfg in
    let pi = UF.create () in (* empty union find data structure *)
    Set.iter (fun reg -> UF.add pi (Reg reg); UF.add pi (Mem reg)) regs; (* for all regs p, add p and p[] *)
    let rec union' pi x y =
      let x = UF.find pi x in
      let y = UF.find pi y in
      if x != y then
        UF.union pi x y;
        match x,y with
          | Reg xr, Reg yr -> union' pi (Mem xr) (Mem yr)
          | _ -> ()
    in
    let edge (_,a,_) = match a with (* no pointer arithmetic! *)
      (* x = y *)
      | Assign (x, Lval (Var y)) ->
          union' pi (Reg x) (Reg y)
      (* x = *y *)
      | Load (x, Lval (Var y))
      (* x = y[e] array accesses get normalized in cfg.ml: y[e] -> rr = M[ry+re] *)
      | Load (x, Binop (Lval (Var y), Add, _))
      (* y[e] = x *)
      | Store (Lval (Var y), Lval (Var x))
      | Store (Binop (Lval (Var y), Add, _), Lval (Var x)) ->
          union' pi (Reg x) (Mem y)
      | _ -> ()
    in
    Set.iter edge cfg; (* build equivalence classes *)
    let show = function Reg r -> r | Mem r -> r^"[]" in
    let edges = ExtList.flat_map (fun reg ->
      let f k1 =
        let k2 = UF.find pi k1 in
        Printf.sprintf "\t\"%s\" -> \"%s\"\n" (show k1) (show k2)
      in
      [f (Reg reg); f (Mem reg)]
    ) (Set.elements regs) in
    Printf.fprintf stderr "digraph {\n%s\n}" (String.concat "" edges)
end
