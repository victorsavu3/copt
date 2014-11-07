include BatteriesExceptionless

exception Not_implemented
exception Todo of string
let (??) m = raise @@ Todo m

(*let debug m = Printf.sprintf ("DEBUG: "^^m^^"\n")*)
let debug m = Printf.fprintf stderr ("DEBUG: "^^m^^"\n")

module Config = struct
  (* intraprocedural: programs consist of just one function 'main' which will be the whole CFG, no globals *)
  let no_fun = true
end

(* some extensions to batteries modules *)
module ExtSet = struct
  include Set
  (*let flatten = flip (fold union) empty*)
  let flatten s = fold union s empty
  let flat_map f = flatten % map f
end
