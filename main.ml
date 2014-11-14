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
  "reach", "CFG after elimination of unreachable nodes (done for everything below)";
  "skip", "CFG after elimination of Skip-edges";
  "memo", "CFG after memorization transformation";
  (*"avail", "CFG with available expressions";*)
  "redelim", "CFG after simple redundancy elimination";
  (*"copyprop", "CFG after copy propagation";*)
  (*"live", "CFG with live registers";*)
  "deadasn", "CFG after dead assignment elimination";
  "all", "CFG after all optimizations";
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
  | "reach" -> from_decls ast |> NonReachElim.transform |> pretty_cfg
  | "skip" -> from_decls ast |> SkipElim.transform |> pretty_cfg
  | "memo" ->
      from_decls ast
      |> NonReachElim.transform
      |> Memorization.transform
      |> pretty_cfg
  | "redelim" ->
      from_decls ast
      |> NonReachElim.transform
      |> Memorization.transform
      |> RedElim.transform
      |> pretty_cfg
  | "deadasn" ->
      from_decls ast
      |> NonReachElim.transform
      |> Memorization.transform
      |> RedElim.transform
      (*|> CopyProp.transform*)
      |> DeadAsnElim.transform
      |> pretty_cfg
  | "all" ->
      from_decls ast
      |> NonReachElim.transform
      |> Memorization.transform
      |> RedElim.transform
      (*|> CopyProp.transform*)
      |> DeadAsnElim.transform
      |> SkipElim.transform
      |> pretty_cfg
  | _ -> "Unimplemented command- see usage!"
