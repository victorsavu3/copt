open Prelude
open Printf
open Cfg
open Transform

let print_ana (module A: Analyses.S) = tap @@ print_endline % (Analyses.pretty_ana (module A))
let program = [
  "Single commands", [
    "print", "Pretty print parsed input program", identity;
  ];
  "Output the CFG/analysis results in dot-format", [
    "out", "output just the CFG", tap (print_endline%pretty_cfg);
    "avail", "CFG with available expressions", print_ana (module (Analyses.AvailExpr (Memorization)));
    "live", "CFG with live registers", print_ana (module Analyses.Liveness);
    "cpana", "CFG with constant propagation results", print_ana (module Analyses.Liveness);
  ];
  "Composable transformations on the CFG", [
    "ident", "don't change anything", identity;
    "reach", "elimination of unreachable nodes", NonReachElim.transform;
    "skip", "elimination of Skip-edges", SkipElim.transform;
    "memo", "memorization transformation", Memorization.transform;
    "redelim", "simple redundancy elimination", RedElim.transform;
    (*"copyprop", "CFG after copy propagation";*)
    "constprop", "constant propagation", ConstProp.transform;
    "deadasn", "dead assignment elimination", DeadAsnElim.transform;
    "all", "all optimizations", fun cfg -> NonReachElim.transform cfg |> Memorization.transform |> RedElim.transform |> ConstProp.transform |> DeadAsnElim.transform |> SkipElim.transform;
  ];
  ]
let records = ExtList.flat_map snd program
let commands = records |> List.map Tuple3.first
let record_for_cmd cmd = List.find ((=) cmd % Tuple3.first) records |> Option.get
let fun_for_cmd = Tuple3.third % record_for_cmd

let print_usage ?cmd () =
  let cmds = ExtString.map_unlines (fun (n,d,f) -> sprintf "\t\t%s\t%s" n d) in
  let sections = ExtString.map_unlines (fun (n,xs) -> sprintf "\t%s\n%s" n (cmds xs)) in
  (match cmd with Some cmd -> print_endline ("Unknown command: " ^ cmd) | None -> ());
  print_endline @@
  "usage: " ^ Sys.argv.(0) ^ " <command1,command2...> [<file>]\n
  Commands:\n" ^ sections program ^ "\n
  Example: " ^ Sys.argv.(0) ^ " reach,memo,avail,redelim,skip,out file.c";
  exit 1

let _ =
  let cmd, cin = match Array.to_list Sys.argv with
    | [bin; cmd] -> cmd, stdin
    | [bin; cmd; path] -> cmd, open_in path
    | _ -> print_usage ()
  in
  let cmds = String.nsplit ~by:"," cmd in
  (*don't even try to parse if one of the commands doesn't exist*)
  List.iter (fun cmd -> if not @@ List.mem cmd commands then print_usage ~cmd:cmd ()) cmds;
  let parse = Simc_pars.decls Simc_lex.ctok % Lexing.from_channel in
  let ast = parse cin in
  match cmd with
  (* handle single commands *)
  | "print" -> print_endline @@ Simc.declsToString ast
  (* composable commands *)
  | _ -> let cfg = from_decls ast in
      let compose cfg cmd = cfg |> fun_for_cmd cmd in
      ignore @@ List.fold_left compose cfg cmds
