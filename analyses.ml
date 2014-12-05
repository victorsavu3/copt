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
    type t = (K.t, K.t) Hashtbl.t * (K.t, int) Hashtbl.t
    (*Exercise 7.3*)
    let create () = Hashtbl.create 16, Hashtbl.create 8
    let add (m,_) k = Hashtbl.add m k k
    let rec find (m,s) k =
      let p = Hashtbl.find m k |? k in (* look up parent *)
      if p=k then p else
        let r = find (m,s) p in (* find root *)
        Hashtbl.add m k r; (* update k to point to root *)
        r
    let union (m,s) x y =
      let size k = Hashtbl.find s k |? 1 in
      let tx,sx = find (m,s) x, size x in
      let ty,sy = find (m,s) y, size y in
      if tx <> ty then ( (* different roots *)
        let a, b = (if sx<sy then tx,ty else ty,tx) |> K.order in
        Hashtbl.add m a b; (* append a to b *)
        Hashtbl.add s b (sx+sy) (* update size *)
      )
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
      (*?? "Exercise 7.3"*)
      let x = UF.find pi x in
      let y = UF.find pi y in
      if x <> y then (
        UF.union pi x y;
        match x,y with
        | Reg x, Reg y -> union' pi (Mem x) (Mem y)
        | _ -> ()
      )
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

module Predominators (C: Cfg) = struct
  module Ana = struct
    let dir = `Fwd
    module D = Domain.NodeMustSet (C)
    let init = D.of_set @@ Cfg.start_nodes C.cfg

    let effect a d = failwith "GenFramework.effect shouldn't be used"
    let effect' (_,_,v) d = D.add v d
  end

  module Csys = GenCsysGenerator (Ana)
  let vals = Csys.solve C.cfg
  let dominates u v = Ana.D.mem u (vals v)
end
