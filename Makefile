TARGET = main.native
#export OCAMLRUNPARAM='b'

all:
	ocamlbuild -use-ocamlfind -use-menhir $(TARGET)

yacc:
	ocamlbuild -use-ocamlfind $(TARGET)

clean:
	ocamlbuild -clean

setup:
	opam update
	opam switch 4.02.1
	eval `opam config env`
	opam install batteries menhir
	# dev stuff you might want
	#opam install utop merlin utop ocp-index ocp-indent
