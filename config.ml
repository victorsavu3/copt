(* intraprocedural: programs consist of just one function 'main' which will be the whole CFG, no globals *)
let no_fun = false
let solver = `Worklist
let max_loopinv = 2
