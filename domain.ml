open Prelude

module type Printable = sig
  type t
  val show: t -> string
end

module type Lattice = sig
  include Printable
  val leq: t -> t -> bool
  val join: t -> t -> t
  val bot: t
end

module BaseSet (Elt: Printable) = struct
  module Base = struct
    (*let leq2compare x y = match leq x y, leq y x with true,false -> -1 | false,true -> 1 | _ -> 0*)
    include Set.Make(struct include Elt let compare = compare end)
    let show s = "{ " ^ (to_list s |> List.map Elt.show |> String.concat ", ") ^ " }"
  end
  module Sub = struct
    include Base
    let leq = subset
    let join = union
    let bot = empty
  end
  module Sup (Bot: sig val bot: Elt.t Set.t end) = struct
    include Base
    let leq = flip subset
    let join = inter
    let bot = Bot.bot |> Set.to_list |> of_list
  end
end

module ExprBaseSet = BaseSet (struct type t = Simc.expr let show = Simc.exprToString end)
module ExprSubSet = ExprBaseSet.Sub
module ExprSupSet (C: Cfg.Cfg) = ExprBaseSet.Sup (struct let bot = Cfg.expr_of_cfg C.cfg end)

module Flat (Base: Printable) : Lattice = struct
  type t = [`Top | `Lifted of Base.t | `Bot]
  let show = function `Top -> "Top" | `Bot -> "Bot" | `Lifted x -> Base.show x
  let leq = curry @@ function _, `Top | `Bot, _ -> true | `Lifted x, `Lifted y when x <= y -> true | _ -> false
  let join = curry @@ function `Bot, x | x, `Bot -> x | x, y when x = y -> x | _ -> `Top
  let bot = `Bot
  let lift x = `Lifted x
end

module FlatInt = Flat (struct type t = int let show = string_of_int end)
