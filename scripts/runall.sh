#!/bin/bash
action=${1:-all}
dir=protocheck/test/samples/bspl
for file in ${dir}/*
do
    echo $file >&2
    python -m protocheck.bspl $action -qs $file
done
