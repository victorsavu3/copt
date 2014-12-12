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
    let module Ana = Analyses.AvailExprMemo (Memorization) (struct let cfg = cfg end) in
    let edge = function
      (*| _ -> ?? "Exercise 3.2c"*)
      | (u, Assign (r, e), v) when Memorization.is_memo r && Ana.available_at e u -> [u, Skip, v]
      | k -> [k]
    in
    map edge cfg
end

module NonReachElim : S = struct
  let transform cfg =
    let rec dfs seen x =
      (*?? "Exercise 4.1a"*)
      if Set.mem x seen then Set.empty else
      out_edges x cfg
      |> comp21 Set.union @@ ExtSet.flat_map (dfs (Set.add x seen) % Tuple3.third)
    in
    dfs Set.empty start_node
end

module DeadAsnElim : S = struct
  let transform cfg =
    let module Ana = Analyses.Liveness (struct let cfg = cfg end) in
    let edge = function
      (*| _ -> ?? "Exercise 4.1c"*)
      | u, Assign (r, e), v
      | u, Load (r, e), v when Ana.dead_at r v -> [u, Skip, v]
      | k -> [k]
    in
    map edge cfg
end

module SkipElim : S = struct
  let transform cfg =
    (*?? "Exercise 5.2a"*)
    let rec next seen u = match out_edges u cfg |> Set.to_list with
      | [u, Skip, v] when not @@ Set.mem v seen -> next (Set.add u seen) v
      | _ -> u
    in
    Set.map (Tuple3.map3 (next Set.empty)) cfg |> NonReachElim.transform
end

module ConstProp : S = struct
  let transform cfg =
    let module Ana = Analyses.ConstProp (struct let cfg = cfg end) in
    (*handle dead code & constants*)
    let edge = function
      (*| _ -> ?? "Exercise 6.2b"*)
      | u, _, v when Ana.dead_at u || Ana.dead_at v -> []
      | u, Assign (r, e), v -> [u, Assign (r, Ana.const u e), v]
      | u, Load (r, e), v -> [u, Load (r, Ana.const u e), v]
      | u, Store (e1, e2), v -> [u, Store (Ana.const u e1, Ana.const u e2), v]
      | u, Neg (e), v when Ana.const u e = Val 0 -> [u, Skip, v]
      | u, Pos (e), v -> [u, (match Ana.const u e with Val x when x<>0 -> Skip | _ -> Pos (e)), v]
      | k -> [k]
    in
    map edge cfg
end

module PartRedElim : S = struct
  let memo_registers : (expr,reg) Hashtbl.t = Hashtbl.create 16

  let t_expr expr =
    match Hashtbl.find memo_registers expr with
    | Some r -> r
    | None ->
      let r = nr () ^ "_memo" in
      Hashtbl.add memo_registers expr r;
      r

  let replace_expr = map (List.singleton % map_edge (Mexpr (var%t_expr)))

  let transform cfg =
    let module CFG = struct let cfg = cfg end in
    let module Avail = Analyses.AvailExpr (CFG) in
    let module Busy = Analyses.VeryBusyExpr (CFG) in
    let module D = Avail.Ana.D in
    let memo_edges exprs v = D.fold (fun e (v,s) ->
        let w = nn () in
        w, Set.add (w, Assign (t_expr e, e), v) s
      ) exprs (v, Set.empty)
    in
    let edge (u,a,v) =
      let evals = D.diff (Busy.vals v) (Avail.Ana.effect a (D.union (Avail.vals u) (Busy.vals u))) in
      let w,xs = memo_edges evals v in
      [u, a, w] @ Set.elements xs
    in
    let init_evals = ExtSet.flat_map (fun v0 -> snd @@ memo_edges (Busy.vals v0) v0) (start_nodes cfg) in
    map edge cfg |> Set.union init_evals |> replace_expr
end

module AstLoopInv = struct
  let transform ast =
    let f = function
      | While (e, xs) -> IfThenElse (e, DoWhile (xs, e), Nop)
      | s -> s
    in
    map_stmts f ast
end

module LoopInv : S = struct
  let transform cfg =
    let module Ana = Analyses.Predominators (struct let cfg = cfg end) in
    let branches n =
      let rec f aa visited u =
        if Set.mem u visited then None else
        match out_edges u cfg |> Set.to_list with
        | [_, Pos _, _ as pos; _, Neg _, _ as neg]
        | [_, Neg _, _ as neg; _, Pos _, _ as pos] ->
            Some (aa,pos,neg) (* found guards *)
        | [_,a,v] -> f (a::aa) (Set.add u visited) v (* continue search *)
        | _ -> None (* end node or malformed *)
      in f [] Set.empty n
    in
    let fold_actions aa u = List.fold_right (fun a (u,ks) ->
        let v = nn () in
        v, (u, a, v)::ks
      ) aa (u, [])
    in
    let edge (u,a,v as k) =
      (*?? "Exercise 8.2"*)
      if not @@ Ana.dominates v u then [k] else
      match branches v with (* we have a back edge *)
      | Some (aa,(_,pos,vp),(_,neg,vn)) when List.length aa <= Config.max_loopinv ->
          let w = nn () in
          let v', aa_edges = fold_actions aa w in
          (u, a, w) :: aa_edges @ [v', pos, vp; v', neg, vn]
      | _ -> [k]
    in
    map edge cfg
end

module PartDeadAsn : S = struct
  let transform cfg =
    let module D = Analyses.DelayableAsn (struct let cfg = cfg end) in
    let module L = Analyses.Liveness (struct let cfg = cfg end) in
    let to_action (x,e) = Assign (x,e) in
    let fss1 a u = D.Ana.D.diff (D.vals u) (D.Ana.effect a (D.vals u)) |> D.Ana.D.to_set  |> Set.filter (fun (x,_) -> L.live_at x u) |> Set.map to_action in
    let fss2 a u v = D.Ana.D.diff (D.Ana.effect a (D.vals u)) (D.vals v) |> D.Ana.D.to_set |> Set.filter (fun (x,_) -> L.live_at x v) |> Set.map to_action in
    let fold_actions xs u = Set.fold (fun a (u,s) ->
        let v = nn () in
        v, Set.add (u, a, v) s
      ) xs (u,Set.empty) |> Tuple2.map2 Set.to_list
    in
    let edge = function
      | u, (Assign (x, e) as a), v ->
          let w1, ss1 = fold_actions (fss1 a u) u in
          let w2, ss2 = fold_actions (fss2 a u v) w1 in
          ss1 @ ss2 @ [w2, Skip, v] (* what about this Skip (not on the slides)? *)
      | u, a, v ->
          let w1, ss1 = fold_actions (fss1 a u) u in
          let w2 = nn () in
          let v', ss2 = fold_actions (fss2 a u v) w2 in
          ss1 @ (w1, a, w2) :: ss2 @ [v', Skip, v]
    in
    let end_edges =
      let ve' = nn () in
      ExtSet.flat_map (fun ve -> Set.map (fun d -> ve, to_action d, ve') (D.vals ve |> D.Ana.D.to_set)) (end_nodes cfg)
    in
    map edge cfg |> Set.union end_edges
end
