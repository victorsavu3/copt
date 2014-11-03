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
      ?? "Exercise 3.2a"
  end
end

module type Framework = sig
  val dir: [`Fwd | `Bwd]
  module D: Domain.Lattice
  val init: D.t
  val effect: action -> D.t -> D.t
end

module CsysGenerator (F: Framework) = struct
  include ConstraintSystem (F.D)
  let constrnt_of_edge (u,a,v) = match F.dir with
    | `Fwd -> v, fun vals -> F.effect a (vals u)
    | `Bwd -> u, fun vals -> F.effect a (vals v)
  let init_constrnts cfg =
    let init_nodes = (match F.dir with `Fwd -> start_nodes | `Bwd -> end_nodes) cfg |> Set.to_list in
    List.map (fun n -> n, const F.init) init_nodes
  let csys_of_cfg : cfg -> csys = fun cfg ->
    let xs = List.map constrnt_of_edge @@ Set.elements cfg in
    init_constrnts cfg @ xs
end