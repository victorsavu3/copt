open Prelude
module Format = Legacy.Format

(*signatures*)
module type Printable = sig
  type t
  val show: t -> string
  val pp: Format.formatter -> t -> unit
end

module type Lattice = sig
  include Printable
  val leq: t -> t -> bool
  val join: t -> t -> t
  val bot: t
end
module type ToppedLattice = sig
  include Lattice
  val top: t
  val meet: t -> t -> t
end

(*general*)
let no_prefix = List.fold_right ExtString.remove ["Simc."; "Domain."]

module Flat (Base: Printable) = struct
  type t = Bot | Val of Base.t | Top [@@deriving show]
  (*let show = function Top -> "Top" | Bot -> "Bot" | Val x -> Base.show x*)
  let leq = curry @@ function _, Top | Bot, _ -> true | Val x, Val y when x <= y -> true | _ -> false
  let join = curry @@ function Bot, x | x, Bot -> x | x, y when x = y -> x | _ -> Top
  let meet = curry @@ function Top, x | x, Top -> x | x, y when x = y -> x | _ -> Bot
  let bot = Bot
  let top = Top
  let lift x = Val x
end

module FlatInt = Flat (struct type t = int [@@deriving show] end)

(*sets*)
module BaseSet (Elt: Printable) = struct
  module Base = struct
    (*let leq2compare x y = match leq x y, leq y x with true,false -> -1 | false,true -> 1 | _ -> 0*)
    include Set.Make(struct include Elt let compare = compare end)
    let show s = "{ " ^ (to_list s |> List.map Elt.show |> String.concat ", ") ^ " }"
    let pp fmt s = failwith "TODO BaseSet.Base.pp"
    let of_set = of_list % Set.to_list
    let to_set = Set.of_list % to_list
  end
  module May = struct
    include Base
    let leq = subset
    let join = union
    let bot = empty
  end
  module Must (Bot: sig val bot: Elt.t Set.t end) = struct
    include Base
    let leq = flip subset
    let join = inter
    let bot = of_set Bot.bot
  end
end

module ExprSet = BaseSet (struct type t = Simc.expr [@@deriving show] end)
module ExprMaySet = ExprSet.May
module ExprMustSet (C: Cfg.Cfg) = ExprSet.Must (struct let bot = Cfg.expr_of_cfg C.cfg end)

module RegSet = BaseSet (struct type t = Cfg.reg [@@deriving show] end)
module RegMaySet = RegSet.May
module RegMustSet (C: Cfg.Cfg) = RegSet.Must (struct let bot = Cfg.regs_of_cfg C.cfg end)

module NodeSet = BaseSet (struct type t = Cfg.node [@@deriving show] end)
module NodeMaySet = NodeSet.May
module NodeMustSet (C: Cfg.Cfg) = NodeSet.Must (struct let bot = Cfg.nodes C.cfg end)

module AsnSet = BaseSet (struct type t = Cfg.reg*Simc.expr [@@deriving show] end)
module AsnMaySet = AsnSet.May
module AsnMustSet (C: Cfg.Cfg) = AsnSet.Must (struct let bot = Cfg.assigns_of_cfg C.cfg end)

(*maps*)
module BaseMap (K: Printable) = struct
 module Base = struct
   module M = Map.Make (struct include K let compare = compare end)
   let show_base val_show x = "{ " ^ String.concat ", " (List.map (fun (k,v) -> K.show k ^ " -> " ^ val_show v) (M.bindings x)) ^ " }"
   let pp fmt x = failwith "TODO BaseMap.pp"
   let add = M.add
   let map2 ?sum:(sum=true) f m1 m2 =
     if m1 == m2 then m1 else
     M.merge (fun k v1 v2 -> match v1, v2 with
     | Some a, Some b -> Some (f a b)
     | Some x, _ | _, Some x when sum -> Some x
     | _ -> None) m1 m2
 end
 module May (V: Lattice) = struct
   include Base
   module V = V
   type t = V.t M.t
   let show = show_base V.show
   let find k m = try M.find k m with Not_found -> V.bot
   (*for each k/v in m1, the same k must be in m2 with a geq v*)
   let leq m1 m2 =
     let p k v = V.leq v (find k m2) in
     m1 == m2 || M.for_all p m1
   let join = map2 V.join
   let bot = M.empty
 end
 module Must (V: ToppedLattice) = struct
   include Base
   type t = Bot | Vals of V.t M.t
   let show = function Bot -> "Bot" | Vals m -> show_base V.show m
   let find k m = try M.find k m with Not_found -> V.top
   (*for each k/v in m2, the same k must be in m1 with a leq v*)
   let leq_vals m1 m2 =
     let p k v = V.leq (find k m1) v in
     m1 == m2 || M.for_all p m2
   let leq = curry @@ function Bot,_ -> true | Vals m1,Vals m2 -> leq_vals m1 m2 | _ -> false
   let join = curry @@ function Bot,x | x,Bot -> x | Vals m1,Vals m2 -> Vals (map2 ~sum:false V.join m1 m2)
   let bot = Bot
   let top = Vals M.empty
 end
end

module RegMap = BaseMap (struct type t = Cfg.reg [@@deriving show] end)
