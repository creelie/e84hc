#!/bin/sh
# Track T4 (natural objects at n = 4), round 12: all exact and mod-p
# computations of the track, then the verifier's scripts.  New logs go to
# rerun/, so that the transcripts in transcripts/ stay as they were.
set -e
cd "$(dirname "$0")"
mkdir -p rerun
export PYTHONDONTWRITEBYTECODE=1
for d in 1 2 3; do python3 -B t4_basic.py $d > rerun/basic_d$d.log; done
for d in 1 2 3; do python3 -B t4_lg.py $d > rerun/lg_d$d.log; done
for nd in "2 1" "2 2" "3 1" "3 2" "4 1" "4 2"; do set -- $nd; python3 -B t4_lg_n.py $1 $2 > rerun/lg_n$1_d$2.log; done
for d in 1 2; do python3 -B t4_contr.py $d > rerun/contr_d$d.log; done
python3 -B t4_example.py 1 small > rerun/example_d1_small.log
python3 -B t4_example.py 1 > rerun/example_d1_ref.log
python3 -B t4_example.py 2 > rerun/example_d2_ref.log
for d in 1 2; do python3 -B t4_minimal.py $d > rerun/minimal_d$d.log; done
python3 -B t4_subtori_search.py 1 3 > rerun/subtori_search_d1.log
for dH in "1 10" "2 8" "3 8"; do set -- $dH; python3 -B t4_sublattice.py $1 $2 > rerun/sublattice_d$1.log; done
python3 -B t4_n2_cross.py > rerun/n2_cross.log
# the verifier's scripts
for d in 1 2 3; do python3 -B verify/v1_relations.py $d > rerun/v1_d$d.log; done
python3 -B verify/v2_lattice.py > rerun/v2_lattice.log
for d in 1 2; do python3 -B verify/v3_tspace.py $d > rerun/v3_d$d.log; done
python3 -B verify/v4_search.py > rerun/v4_search.log
python3 -B verify/v5_chi.py > rerun/v5_chi.log
echo done
