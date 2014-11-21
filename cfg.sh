#!/bin/bash
trap 'kill 0' SIGINT SIGTERM EXIT

splitgraphs=($(cat | awk -vRS="}" '{gsub(/ |\t|\n/, ""); printf $0" "}'))
for i in ${splitgraphs[@]}
do
	echo "$i}" | dot -Tpng | display png:- &
done
wait
