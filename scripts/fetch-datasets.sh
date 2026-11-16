#!/bin/sh
# Download the MBA datasets collected by GAMBA (GPL-3.0, not vendored here) into bench-data/.
set -e
dir="$(dirname "$0")/../bench-data"
mkdir -p "$dir"
base=https://raw.githubusercontent.com/DenuvoSoftwareSolutions/GAMBA/main/experiments/datasets
for f in neureduce mba_obf_linear mba_obf_nonlinear syntia mba_flatten qsynth_ea bonus/loki_tiny; do
    curl -fsSL -o "$dir/$(basename "$f").txt" "$base/$f.txt"
done
ls -l "$dir"
