#!/bin/bash

set -euxo pipefail

for prog in *.pl; do
    output="${prog}.out"
    swipl -l "${prog}" -g 'visible(+all)' -g 'leash(-all)' -g trace -g go -g halt > "${output}" 2>&1
    ./tracetool --input "${output}" fmt --output "${prog}.trace"
    ./tracetool --input "${output}" states > "${prog}.states"
done
