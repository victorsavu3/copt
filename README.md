copt
====

Program optimizer for CMA C.

Biggest simplifications:
 * only int constants, fewer operators
 * no casts, no typedef
 * no function pointer type --- difficult to parse, also we don't care
 * no semicolon after "struct n {...}"

Build
-----

Install [opam](https://opam.ocaml.org/doc/Install.html), then do

       git clone https://github.com/vogler/copt.git
       cd copt
       make setup
       make

Menhir is optional, you can use `make yacc` to compile using ocamllex/ocamlyacc instead.
