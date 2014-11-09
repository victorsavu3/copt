open Prelude
open Cfg
open Solver

module AvailExpr (C: Cfg) (Memo: sig val is_memo: reg -> bool end) = struct
  module Ana = struct
    let dir = `Fwd
    module D = Domain.ExprSupSet (C)
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
  module Sol = Csys.RoundRobin

  let av = Sol.solve @@ Csys.csys_of_cfg C.cfg
  let available_at e u = Ana.D.mem e (av u)
end

module Liveness (C: Cfg) = struct
  module Ana = struct
    let dir = `Bwd
    module D = Domain.RegSupSet (C)
    let init = D.bot

    let dregs e = regs e |> Set.to_list |> D.of_list
    let effect a d = match a with
      | Pos (e) -> D.union d (dregs e)
      | Neg (e) -> D.union d (dregs e)
      | Assign (r, e) when D.mem r d -> D.union (D.remove r d) (dregs e)
      | Assign (r, e) -> D.remove r d
      | Load (r, e) when D.mem r d -> D.union (D.remove r d) (dregs e)
      | Load (r, e) -> D.remove r d
      | Store (e1, e2) -> D.union d (D.union (dregs e1) (dregs e2))
      | _ -> d
  end

  module Csys = CsysGenerator (Ana)
  module Sol = Csys.RoundRobin

  let lv = Sol.solve @@ Csys.csys_of_cfg C.cfg
  let live_at r u = Ana.D.mem r (lv u)
  let dead_at r u = not @@ live_at r u
end
