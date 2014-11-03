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
      | _ -> ?? "Exercise 3.2b"
  end

  module Csys = CsysGenerator (Ana)
  module Sol = Csys.RoundRobin

  let av = Sol.solve @@ Csys.csys_of_cfg C.cfg
  let available_at e u = Ana.D.mem e (av u)
end
