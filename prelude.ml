include Batteries

exception Not_implemented
exception Todo of string
let (??) m = raise @@ Todo m

(* some extensions to batteries modules *)
module ExtSet = struct
  include Set
  (*let flatten = flip (fold union) empty*)
  let flatten s = fold union s empty
  let flat_map f = flatten % map f
end
