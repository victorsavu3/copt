include BatteriesExceptionless

exception Not_implemented
exception Todo of string
let (??) m = raise @@ Todo m

(*let debug m = Printf.sprintf ("DEBUG: "^^m^^"\n")*)
let debug m = Printf.fprintf stderr ("DEBUG: "^^m^^"\n")

let comp21 f g x = f x (g x)
let comp22 f g x y = f (g x) (g y)
let comp23 f g h x = f (g x) (h x)

(* some extensions to batteries modules *)
module ExtSet = struct
  include Set
  (*let flatten = flip (fold union) empty*)
  let flatten s = fold union s empty
  let flat_map f = flatten % map f
end
