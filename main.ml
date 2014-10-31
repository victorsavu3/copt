open Prelude
open Printf

let parse = Simc_pars.decls Simc_lex.ctok % Lexing.from_channel

open Cfg
open Transform
open Domain
open Analyses

let commands = [
  "print", "Pretty print parsed input";
  "cfg", "Output the unmodified CFG in dot-format";
  "memo", "CFG after memorization transformation";
  "avail", "CFG with available expressions";
  "redelim", "CFG after simple redundancy elimination";
  ]

let print_usage () = print_endline @@
  "usage: " ^ Sys.argv.(0) ^ " <command> [<file>]\n
  Commands:\n" ^ String.concat "\n" @@ List.map (uncurry @@ sprintf "\t%s\t%s") commands;
  exit 1

let _ =
  let cmd, cin = match Array.to_list Sys.argv with
    | [bin; cmd] -> cmd, stdin
    | [bin; cmd; path] -> cmd, open_in path
    | _ -> print_usage ()
  in
  (*don't even try to parse if the command doesn't exist*)
  if not @@ List.mem cmd @@ List.map fst commands then print_usage () else
  let ast = parse cin in
  print_endline @@ match cmd with
  | "print" -> Simc.declsToString ast
  | "cfg" -> from_decls ast |> pretty_cfg
  | "memo" ->
      from_decls ast
      |> transform (module Memorization)
      |> pretty_cfg
  | "redelim" ->
      let cfg = from_decls ast
      |> transform (module Memorization) in
      transform (module RedElim (struct let cfg = cfg end)) cfg
      |> pretty_cfg
  | _ -> "Unimplemented command- see usage!"
