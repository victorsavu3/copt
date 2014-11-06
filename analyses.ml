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
      | Pos e -> d
      | Neg e -> d
      | Assign (r, e) -> let res = (if Memo.is_memo r then (D.add e d) else d) in (D.filter (fun ex -> Simc.reg_in_expr r ex) res)
      | Load (r, e) -> D.filter (fun ex -> Simc.reg_in_expr r ex) d
      | Store (e1, e2) -> d
      | Skip -> d
      | Call (r, n, args) -> d
  end

  module Csys = CsysGenerator (Ana)
  module Sol = Csys.RoundRobin

  let av = Sol.solve @@ Csys.csys_of_cfg C.cfg
  let available_at e u = Ana.D.mem e (av u)
end
