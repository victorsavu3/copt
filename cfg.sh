#!/bin/bash
# trap 'kill 0' SIGINT SIGTERM EXIT

splitgraphs=($(cat | awk -vRS="digraph" '{gsub(/ |\t|\n/, ""); printf $0" "}'))
for i in ${splitgraphs[@]}
do
  echo "digraph$i" | dot -Tpng | display png:- &
done
wait
