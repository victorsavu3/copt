open Prelude
open Cfg

module ConstraintSystem (D: Domain.Lattice) = struct
  type var = node
  type value = D.t
  type valuation = var -> value
  type rhs = valuation -> value
  type constrnt = var * rhs
  type csys = constrnt list
  module type Solver = sig
    val solve: csys -> valuation
  end

  (* we should use a map for iterating *)
  let val_of : (var, value) Map.t -> valuation = fun vals n ->
    Map.find n vals |? D.bot

  module RoundRobin : Solver = struct
    let solve : csys -> valuation = fun csys ->
      (*?? "Exercise 3.2a"*)
      let n = ref 0 in
      let round vals =
        ignore (debug "### Round %i ###" !n); incr n;
        List.iter (fun (v,rhs) -> ignore (debug "A[%s] = %s" (show_node v) (D.show (val_of vals v)))) csys;
        List.fold_right (fun (lhs,fi) (vals, fin) ->
          let lhs_val = val_of vals lhs in
          let rhs_val = fi (val_of vals) in
          let new_val = D.join lhs_val rhs_val in
          (*debug "A[%i]: old: %s, new: %s" lhs (D.show lhs_val) (D.show rhs_val);*)
          if D.leq new_val lhs_val then
            vals, fin (* value not changed *)
          else
            Map.add lhs new_val vals, false
        ) csys (vals, true)
      in
      let rec iterate vals = let vals, fin = round vals in if fin then vals else iterate vals in
      val_of @@ iterate Map.empty
  end

  module Worklist (Deps: sig val depend_on: var -> constrnt list end) : Solver = struct
    let solve : csys -> valuation = fun csys ->
      (*?? "Exercise 5.2b"*)
      let rec step vals = function
        | [] -> vals (* done *)
        | (lhs,fi)::w ->
            let lhs_val = val_of vals lhs in
            let rhs_val = fi (val_of vals) in
            let new_val = D.join lhs_val rhs_val in
            ignore @@ debug "A[%i]: old: %s, new: %s, join: %s" lhs (D.show lhs_val) (D.show rhs_val) (D.show new_val);
            if D.leq new_val lhs_val then
              step vals w
            else
              let fjs = Deps.depend_on lhs in
              if neg List.is_empty fjs then
                ignore @@ debug "A[%i] changed -> added constraints for nodes {%s} to worklist" lhs (String.concat ", " @@ List.map (show_node%fst) fjs);
              step (Map.add lhs new_val vals) (w @ fjs)
      in
      val_of @@ step Map.empty csys
  end
end

module type Framework = sig
  (*direction*)
  val dir: [`Fwd | `Bwd]
  (*domain*)
  module D: Domain.Lattice
  (*initial value*)
  val init: D.t
  (*abstract effects*)
  val effect: action -> D.t -> D.t
end

module CsysGenerator (F: Framework) = struct
  include ConstraintSystem (F.D)
  let constrnt_of_edge (u,a,v) = match F.dir with
    | `Fwd -> v, fun vals -> F.effect a (vals u)
    | `Bwd -> u, fun vals -> F.effect a (vals v)
  let init_constrnts cfg =
    let init_nodes = (match F.dir with `Fwd -> start_nodes | `Bwd -> end_nodes) cfg |> Set.to_list in
    ignore (debug "init_nodes: %s" (String.concat ", " @@ List.map show_node init_nodes));
    List.map (fun n -> n, const F.init) init_nodes
  let csys_of_cfg : cfg -> csys = fun cfg ->
    let xs = List.map constrnt_of_edge @@ Set.elements cfg in
    init_constrnts cfg @ xs
  let dependencies : cfg -> (var -> constrnt list) = fun cfg ->
    let f (u,_,v as e) =
      let k = match F.dir with `Fwd -> u | `Bwd -> v in
      Map.modify_def [] k (List.cons (constrnt_of_edge e))
    in
    fun k -> Map.find k (Set.fold f cfg Map.empty) |? []
  let solve : cfg -> valuation = fun cfg ->
    let module Solver = (val match Config.solver with
      | `RoundRobin -> (module RoundRobin : Solver)
      | `Worklist -> (module Worklist (struct let depend_on = dependencies cfg end) : Solver)
    ) in
    Solver.solve @@ csys_of_cfg cfg
end
