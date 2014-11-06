open Prelude
open Simc
open Cfg

module type S = sig
  val transform: edge -> edge list
end

let transform (module M : S) = ExtSet.flat_map (Set.of_list % M.transform)

module Memorization = struct (* applicative functor *)
  let memo_registers : (expr,reg) Hashtbl.t = Hashtbl.create 16

  let t_expr expr =
    match Hashtbl.find memo_registers expr with
    | Some r -> r
    | None ->
      let r = nr () ^ "_memo" in
      Hashtbl.add memo_registers expr r;
      r

  let is_memo reg = Hashtbl.values memo_registers |> List.of_enum |> List.mem reg

  let transform = function
    | (u, Pos e, v) ->
        let v1 = nn () in
        let te = t_expr e in
        [u, Assign (te, e), v1;
        v1, Pos (var te), v]
    | (u, Neg e, v) ->
        let v1 = nn () in
        let te = t_expr e in
        [u, Assign (te, e), v1;
        v1, Neg (var te), v]
    | (u, Assign (r, e), v) ->
        let v1 = nn () in
        let te = t_expr e in
        [u, Assign (te, e), v1;
        v1, Assign (r, var te), v]
    | (u, Load (r, e), v) ->
        let v1 = nn () in
        let te = t_expr e in
        [u, Assign (te, e), v1;
        v1, Load (r, var te), v]
    | (u, Store (e1, e2), v) ->
        let v1 = nn () in
        let v2 = nn () in
        let te1 = t_expr e1 in
        let te2 = t_expr e2 in
        [u, Assign (te1, e1), v1;
        v1, Assign (te2, e2), v2;
        v2, Store (var te1, var te2), v]
    | (u, Skip, v) -> [u, Skip, v]
    | (u, Call (r,n,args), v) as edge -> [edge] (* registers are already introduced in cfg *)
end


module RedElim (C: Cfg) : S = struct
  module Ana = Analyses.AvailExpr (C) (Memorization)

  let transform = function
    | (u, Assign (r, e), v) -> if Ana.available_at e u then [u, Skip, v] else [u, Assign (r, e), v]
    | (u, a, v) -> [u, a, v]
end
