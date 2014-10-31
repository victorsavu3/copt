export OCAMLRUNPARAM='b'

for f in tests/*.c; do
    for cmd in print cfg memo; do
        ./main.native $cmd $f > /dev/null || echo -e "Failed: ./main.native $cmd $f\n"
    done
done
