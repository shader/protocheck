#!/bin/bash
action=${1:-all}
dir=samples
for file in ${dir}/*
do
    echo $file >&2
    python -m protocheck.bspl $action -qs $file
done
