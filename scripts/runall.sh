#!/bin/bash
dir=protocheck/test/samples/bspl
for file in (${dir}/*)
do
    python -m protocheck.bspl all -qs ${dir}/${file}
done
