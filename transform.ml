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
    | _ -> ?? "Exercise 2.3"
end
