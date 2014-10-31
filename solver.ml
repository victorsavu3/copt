open Prelude
open Cfg

module ConstraintSystem (D: Domain.Lattice) = struct
  type var = node
  type value = D.t
  type valuation = var -> value
  type rhs = valuation -> value
  type constrnt = var * rhs
  type csys = constrnt Set.t
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
  val effect: action -> D.t -> D.t
end

module CsysGenerator (F: Framework) = struct
  include ConstraintSystem (F.D)
  let constrnt_of_edge (u,a,v) = match F.dir with
    | `Fwd -> v, fun vals -> F.effect a (vals u)
    | `Bwd -> u, fun vals -> F.effect a (vals v)
  let csys_of_cfg : cfg -> csys = Set.map constrnt_of_edge
end
