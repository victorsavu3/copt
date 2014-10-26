open Prelude
open Simc
open Cfg

module type S = sig
  val transform: edge -> edge list
end

let transform (module M : S) = ExtSet.flat_map (Set.of_list % M.transform)

module Memorization : S = struct (* applicative functor *)
  let memo_registers : (expr,reg) Hashtbl.t = Hashtbl.create 16 

  let t_expr expr = 
    match Hashtbl.find_option memo_registers expr with
    | Some r -> r
    | None -> (let r = nr () ^ "_memo" in Hashtbl.add memo_registers expr r; r)

  let transform = function 
    | u, Assign (r, e), v ->
        let w = nn () in
        let te = t_expr e in
        [u, Assign (te, e), w;
         w, Assign (r, var te), v]
    | u, Pos(e), v ->
    	let w = nn () in
        let te = t_expr e in
        [u, Assign (te, e), w;
         w, Pos(Lval(Var(te))), v]
    | u, Neg(e), v ->
    	let w = nn () in
        let te = t_expr e in
        [u, Assign (te, e), w;
         w, Neg(Lval(Var(te))), v]
    | u, Load(reg, e), v ->
    	let w = nn () in
        let te = t_expr e in
        [u, Assign (te, e), w;
         w, Load(reg, Lval(Var(te))), v]
    | u, Store(e1, e2), v ->
    	let w1 = nn () in
    	let w2 = nn () in
        let te1 = t_expr e1 in
        let te2 = t_expr e2 in
        [u, Assign (te1, e1), w1;
         w1, Assign (te2, e2), w2;
         w2, Store(Lval(Var(te1)), Lval(Var(te2))), v]
    | u, x, v ->
      [u, x, v]
    | _ -> ?? "Exercise 2.3"
end
