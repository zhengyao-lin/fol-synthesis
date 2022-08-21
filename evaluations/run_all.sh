#!/bin/bash

set -euf

cat <<EOT
Starting evaluations. You can interrupt this script and restart any time. It will resume from the previous saved point.
EOT

num_cores=$(nproc --all)

results_dir=eval_results
modal_smt_results="$results_dir/modal-smt-results.pickle"
modal_enum_results="$results_dir/modal-enum-results.pickle"

# Uncomment the following line to set a synthesis timeout of 10800 seconds
# for evaluation 2
# modal_enum_timeout=10800

# A utility function to time a command while it's running
run_and_time() {
    timer() {
        start=$(date +%s%2N)
        while true; do
            now=$(date +%s%2N)
            elapsed=$((now - start))
            elapsed=$(printf "%03d\n" $elapsed)
            echo -ne "\033[2K\r    Elapsed: ${elapsed:0:-2}.${elapsed: -2}s" >&2
            sleep 0.01
        done
    }

    clear_timer() {
        kill $1
        wait $1 2>/dev/null

        now=$(date +%s%2N)
        elapsed=$((now - $2))
        elapsed=$(printf "%03d\n" $elapsed)
        echo -ne "\033[2K\r    Took: ${elapsed:0:-2}.${elapsed: -2}s" >&2
    }
    
    timer & timer_pid=$!
    start=$(date +%s%2N)
    trap "clear_timer $timer_pid $start" RETURN
    $@
}

if ! [ -d "$results_dir" ]; then
    mkdir $results_dir
fi

################
# Evaluation 1 #
################
echo
echo "Evaluation 1. Synthesizing modal axioms for 17 modal logics (using constraint solving)."
echo "    Results are saved to $modal_smt_results."
num_jobs=$((num_cores > 17 ? 17 : num_cores))
echo "    Running with $num_jobs parallel jobs."
run_and_time python3 -m evaluations.modal synthesize \
    --continue \
    --save $modal_smt_results \
    -j $num_jobs \
    1>$results_dir/modal-smt-stdout.txt

################
# Evaluation 2 #
################
echo
echo "Evaluation 2. Synthesizing modal axioms for 17 modal logics (using naive enumeration)."
echo "    Results are saved to $modal_enum_results."
num_jobs=$((num_cores > 17 ? 17 : num_cores))
echo "    Running with $num_jobs parallel jobs."
if ! [ -z ${modal_enum_timeout+z} ]; then
    echo "    Synthesis timeout $modal_enum_timeout"
fi
run_and_time python3 -m evaluations.modal synthesize \
    --continue \
    --save $modal_enum_results \
    -j $num_jobs \
    ${modal_enum_timeout+--synthesis-timeout $modal_enum_timeout} \
    --use-enumeration \
    --separate-independence \
    --disable-counterexamples \
    1>$results_dir/modal-enum-stdout.txt
