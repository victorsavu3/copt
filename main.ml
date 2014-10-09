open Prelude

let parse = Simc_pars.decls Simc_lex.ctok % Lexing.from_channel

open Cfg
open Transform
(*open Domain*)

let _ =
  let cin = if Array.length Sys.argv > 1 then open_in Sys.argv.(1) else stdin in
  let ast = parse cin in
  let cfg = from_decls ast in
  (* uncomment to pretty print the parsed input *)
  (*print_endline @@ Simc.declsToString ast; *)
  (* uncomment to print a dot graph of the CFG before the transformation *)
  (*print_endline @@ pretty_cfg cfg; *)
  let cfg = transform (module Memorization) cfg in
  print_endline @@ pretty_cfg cfg
