#!/bin/bash

set -euf

results_dir=eval_results
vampire_path=vampire/vampire_z3_Release_static_master_4764

modal_smt_results="$results_dir/modal-smt-results.pickle"
modal_enum_results="$results_dir/modal-enum-results.pickle"
kleene_smt_results="$results_dir/kleene-smt"
kleene_enum_results="$results_dir/kleene-enum"

cat <<EOT
You can interrupt this script and restart any time.
It will resume from the previous saved point.
EOT

# Uncomment the following line to set a synthesis timeout of 10800 seconds
# for evaluation 2
modal_enum_timeout=60

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
        now=$(date +%s%2N)
        elapsed=$((now - $1))
        elapsed=$(printf "%03d\n" $elapsed)
        echo -ne "\033[2K\r    Took: ${elapsed:0:-2}.${elapsed: -2}s\n" >&2
    }
    
    timer & timer_pid=$!
    start=$(date +%s%2N)
    trap "kill $timer_pid; clear_timer $start" RETURN
    $@
}

bold() {
    echo -ne "\033[1m$@\033[0m"
}

num_cores=$(nproc --all)

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
if ! run_and_time python3 -m evaluations.modal synthesize \
    --continue \
    --save $modal_smt_results \
    -j $num_jobs \
    1>$results_dir/modal-smt-stdout.txt; then
    echo "Evaluation failed."
    exit 1
fi

echo -e "To show the results: $(bold python3 -m evaluations.modal show $modal_smt_results)"

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
if ! run_and_time python3 -m evaluations.modal synthesize \
    --continue \
    --save $modal_enum_results \
    -j $num_jobs \
    ${modal_enum_timeout+--synthesis-timeout $modal_enum_timeout} \
    --use-enumeration \
    --separate-independence \
    --disable-counterexamples \
    1>$results_dir/modal-enum-stdout.txt; then
    echo "Evaluation failed."
    exit 1
fi
cat <<EOT
To show the results: python3 -m evaluations.modal show $modal_enum_results
EOT

################
# Evaluation 3 #
################
echo
echo "Evaluation 3. Synthesizing equational axioms for language structures (using constraint solving)."
if ! run_and_time python3 -m evaluations.kleene \
    --cache $kleene_smt_results \
    --vampire $vampire_path \
    --vampire-pruning \
    1>$results_dir/kleene-smt-stdout.txt; then
    echo "Evaluation failed."
    exit 1
fi
cat <<EOT
To show the results: cat $results_dir/kleene-smt-stdout.txt
EOT

################
# Evaluation 4 #
################
echo
echo "Evaluation 4. Synthesizing equational axioms for language structures (using naive enumeration)."
if ! run_and_time python3 -m evaluations.kleene_enum \
    --vampire $vampire_path \
    1>$results_dir/kleene-enum-stdout.txt; then
    echo "Evaluation failed."
    exit 1
fi
cat <<EOT
To show the results: cat $results_dir/kleene-enum-stdout.txt
EOT
