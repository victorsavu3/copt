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
  let str u = Asol.vals u |> Asol.Ana.D.show in
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
