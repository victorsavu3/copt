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

    let rec getVal = fun e m -> 
      let getBinOpVal : Simc.expr -> binop -> Simc.expr -> V.t = fun a op b ->
        let v = (getVal a m, getVal b m) in
        match v with
          | V.Val va, V.Val vb -> V.Val ((fun_of_op op) va vb)
          | _ -> V.top
      in  
      let ret : V.t = match e with 
        | Simc.Val c -> V.Val c
        | Lval l -> (match l with 
          | Var r -> D.find r m
          | _ -> V.top)
        | Binop (a, op, b) -> getBinOpVal a op b
        | _ -> V.top
      in ret

    let effect = fun a d ->
      match d with
      | D.Bot -> D.bot
      | D.Vals d -> (
        match a with
        | Assign (r, e) -> D.Vals (D.add r (getVal e d) d)
        | Load (r, _) -> D.Vals (D.add r V.top d)
        | Pos(e) when (getVal e d) = (V.Val 0) -> D.bot
        | Neg(e) when (getVal e d) <> (V.Val 0) && (getVal e d) <> (V.top) -> D.bot
        | _ -> D.Vals (d)
      )
        (*?? "Exercise 6.2a" (* you can use fun_of_op for evaluating binops *)*)
  end

  module Csys = CsysGenerator (Ana)
  let cv = Csys.solve C.cfg
  let dead_at u = cv u = Ana.D.Bot
  let val_at u r = 
    let t = match cv u with 
      | Ana.D.Bot -> Ana.V.top 
      | Ana.D.Vals m -> Ana.D.find r m
    in match t with
      | Ana.V.Val c -> Some c
      | _ -> None
      
  let exp_val_at u e = 
    let t = match cv u with 
      | Ana.D.Bot -> Ana.V.top 
      | Ana.D.Vals m -> Ana.getVal e m
    in match t with
      | Ana.V.Val c -> Some c
      | _ -> None
end
