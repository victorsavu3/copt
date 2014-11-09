open Prelude
open Simc
open Cfg

module type S = sig
  val transform: cfg -> cfg
end

let map (f : edge -> edge list) = ExtSet.flat_map (Set.of_list % f)

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

  let transform = map @@ function
    (*| _ -> ?? "Exercise 2.3"*)
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

module RedElim : S = struct
  let transform cfg =
    let module Ana = Analyses.AvailExpr (struct let cfg = cfg end) (Memorization) in
    let edge = function
      (*| _ -> ?? "Exercise 3.2c"*)
      | (u, Assign (r, e), v) when Memorization.is_memo r && Ana.available_at e u -> [u, Skip, v]
      | k -> [k]
    in
    map edge cfg
end

module NonReachElim = struct
  let transform orig =
    let rec dfs : node -> cfg = fun x ->
      let edges = (Set.filter (fun n -> (Tuple3.first n) == x) orig) in
      let dest = Set.map Tuple3.third edges in
        Set.fold Set.union (Set.map dfs dest) edges
    in
    dfs start_node
end

module DeadAsnElim : S = struct
  let transform cfg =
    let module Ana = Analyses.Liveness (struct let cfg = cfg end) in
    let edge = function
      | _ -> ?? "Exercise 4.1c"
    in
    map edge cfg
end
