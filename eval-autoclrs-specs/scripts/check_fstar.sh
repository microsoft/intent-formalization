#!/bin/bash
set -euo pipefail
eval $(opam env)

FSTAR=~/AutoCLRS/FStar/bin/fstar.exe
PULSE_LIB=~/AutoCLRS/pulse/out/lib/pulse
FILE="$1"

$FSTAR --include $PULSE_LIB "$FILE" 2>&1
