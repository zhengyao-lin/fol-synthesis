Synthesizing Axiomatizations with Logic Learning
---

Quick start:



1. Install Python dependencies
```
python3 -m pip install -r requirements.txt
```

2. Download Vampire binary: [https://vprover.github.io/download.html](https://vprover.github.io/download.html)

3. Synthesize modal axioms for 17 modal logics (with constraint solving)
```
python3 -m evaluations.modal synthesize \
    --continue \
    --save modal-results-smt.pickle \
    -j <parallel jobs>
```

To show the results:
```
python3 -m evaluations.modal show modal-results-smt.pickle
```
An option `--enable-plot` can be added to render a visualization of when each axiom is synthesized (requires LaTeX).

4. Synthesize modal axioms for 17 modal logics (with naive enumeration)
```
python3 -m evaluations.modal synthesize \
    --continue \
    --save modal-results-enum.pickle \
    -j <parallel jobs> \
    --synthesis-timeout 10800 \
    --use-enumeration \
    --separate-independence \
    --disable-counterexamples
```

To show the results:
```
python3 -m evaluations.modal show modal-results-enum.pickle
```

5. Synthesize equational axioms for language structures (with constraint solving)
```
python3 -m evaluations.kleene \
    --cache kleene-cache-smt \
    --vampire <path to the Vampire binary> \
    --vampire-pruning
```
The results will be printed to stdout.

6. Synthesize equational axioms for language structures (with naive enumeration)
```
python3 -m evaluations.kleene_enum --vampire <path to the Vampire binary>
```
The results will be printed to stdout.


python3 -m evaluations.modal synthesize \
    --continue \
    --save modal-results-enumeration.pickle \
    -j 17 \
    --synthesis-timeout 600 \
    --use-enumeration \
    --separate-independence \
    --disable-counterexamples

python3 -m evaluations.kleene \
    --cache kleene-cache-smt \
    --vampire /home/zhengyal/work/vampire_z3_Release_static_master_4764 \
    --vampire-pruning
