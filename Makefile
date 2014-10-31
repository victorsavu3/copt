TARGET = main.native

# put this in your environment to enable stacktraces:
#export OCAMLRUNPARAM='b'

all:
	ocamlbuild -use-ocamlfind -use-menhir $(TARGET)

yacc:
	ocamlbuild -use-ocamlfind $(TARGET)

test:
	bash -c tests/all.sh

clean:
	ocamlbuild -clean

setup:
	opam init
	opam update
	opam switch 4.02.1
	eval `opam config env`
	opam install batteries menhir
	# dev stuff you might want
	#opam install utop merlin utop ocp-index ocp-indent
