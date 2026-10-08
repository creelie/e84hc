#!/bin/sh
# Track T1 (quartic CM fields): run every track script and the verifier's
# scripts.  New logs go to rerun/, so that the transcripts in transcripts/
# stay as they were; compare with, for example,
#   diff transcripts/t1_T.log rerun/t1_T.log
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1
mkdir -p rerun
for s in t1_generic t1_T t1_loci t1_annihilator t1_lowerbound t1_fullflat t1_shapes_explore; do
  echo "=== $s ==="; python3 -B $s.py > rerun/$s.log 2>&1; tail -2 rerun/$s.log
done
for s in v_phi v_ann v_fullflat v_binomial v_binomial_9296 v_minsearch; do
  echo "=== verify/$s ==="; python3 -B verify/$s.py > rerun/$s.log 2>&1; tail -2 rerun/$s.log
done
