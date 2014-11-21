open Prelude
open Cfg
open Solver

module AvailExpr (C: Cfg) (Memo: sig val is_memo: reg -> bool end) = struct
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
  let av = Csys.solve C.cfg
  let available_at e u = Ana.D.mem e (av u)
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
  let lv = Csys.solve C.cfg
  let live_at r u = Ana.D.mem r (lv u)
  let dead_at r u = not @@ live_at r u
end

module ConstProp (C: Cfg)= struct
  open Simc
  module Ana = struct
    let dir = `Fwd
    module V = Domain.FlatInt
    module D = Domain.RegMap.Must (V)
    let init = D.top

    let effect a d =
      ?? "Exercise 6.2a" (* you can use fun_of_op for evaluating binops *)
  end

  module Csys = CsysGenerator (Ana)
  let cv = Csys.solve C.cfg
  let dead_at u = cv u = Ana.D.Bot
end
